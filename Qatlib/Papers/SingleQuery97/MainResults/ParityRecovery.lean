/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
import Qatlib.Papers.QComplexity97.XorSeparation.ParityOracleSeparationRestricted
set_option warningAsError false

namespace Qatlib.Papers.SingleQuery97.MainResults.ParityRecovery

open Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib.Concepts.QueryWordCore.QueryMachinery

abbrev parityAnswer {n : ℕ} (x y : DbVec n) : ℕ := dot x y

theorem parityAnswer_comm {n : ℕ} (x y : DbVec n) :
    parityAnswer x y = parityAnswer y x :=
  dot_comm x y

theorem parityAnswer_unitVec {n : ℕ} (i : Fin n) (y : DbVec n) :
    parityAnswer (unitVec i) y = bitVal (y i) :=
  dot_unit i y

theorem parityAnswers_determine_database {n : ℕ} (y y' : DbVec n)
    (h : ∀ x, parityAnswer x y = parityAnswer x y') : y = y' :=
  parity_answers_determine y y' h

theorem parityPhases_determine_database {n : ℕ} (y y' : DbVec n)
    (h : ∀ x, signOfParity (parityAnswer x y) = signOfParity (parityAnswer x y')) :
    y = y' :=
  sign_answers_determine y y' h

theorem bvCharBit_eq_true_iff {n : ℕ} (k x : Reg n) :
    bvCharBit k x = true ↔ dot x k % 2 = 1 := by
  unfold bvCharBit
  rw [decide_eq_true_iff, dot_eq_filter_card]

theorem signOfParity_dot_eq_bvCharBit_phase {n : ℕ} (k x : Reg n) :
    signOfParity (dot x k) =
      if bvCharBit k x then (-1 : ℂ) else 1 := by
  rw [dot_eq_filter_card]
  unfold signOfParity bvCharBit
  have hm := Nat.mod_lt (Finset.univ.filter fun i => k i && x i).card
    (by omega : 0 < 2)
  interval_cases h : (Finset.univ.filter fun i => k i && x i).card % 2 <;>
    simp

theorem singleQuery_recovery {n : ℕ} (k : Reg n) :
    Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
        (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket k) Minus ∧
      QueryCount (bvOneCallCircuit n) = 1 :=
  Qatlib.Papers.QComplexity97.XorSeparation.bv_one_query_recovery n k

theorem singleQuery_recovers_unique_database {n : ℕ} (k : Reg n) :
    (Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
        (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket k) Minus ∧
      QueryCount (bvOneCallCircuit n) = 1) ∧
    (∀ y : Reg n, (∀ x : Reg n, parityAnswer x y = parityAnswer x k) → y = k) :=
  ⟨singleQuery_recovery k, fun y hy => parityAnswers_determine_database y k hy⟩

end Qatlib.Papers.SingleQuery97.MainResults.ParityRecovery
