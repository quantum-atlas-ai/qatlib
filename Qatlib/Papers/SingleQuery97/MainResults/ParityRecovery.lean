/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
import Qatlib.Papers.QComplexity97.XorSeparation.ParityOracleSeparationRestricted

/-!
# Parity answers and single-query database recovery

This module proves that parity answers, and their signs, determine a binary database. It
connects `parityAnswer` with Bernstein–Vazirani phase bits and proves exact recovery with
`bvOneCallCircuit`, together with uniqueness of the recovered database, in the setting of
[TerhalSmolin1998].

## Main statements

* `parityPhases_determine_database`: Two binary databases with equal parity signs for every
  dot-product query are equal.
* `singleQuery_recovers_unique_database`: One oracle query recovers the hidden binary vector
  exactly, and that vector is uniquely determined by all its dot-product answers, as in
  [TerhalSmolin1998].

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

namespace Qatlib.Papers.SingleQuery97.MainResults.ParityRecovery

open Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- The natural-number dot product of two binary database vectors. -/
abbrev parityAnswer {n : ℕ} (x y : DbVec n) : ℕ := dot x y

/-- The binary database dot-product answer is symmetric in the query and database. -/
theorem parityAnswer_comm {n : ℕ} (x y : DbVec n) :
    parityAnswer x y = parityAnswer y x :=
  dot_comm x y

/-- A unit-vector query returns the natural-number value of the selected database bit. -/
theorem parityAnswer_unitVec {n : ℕ} (i : Fin n) (y : DbVec n) :
    parityAnswer (unitVec i) y = bitVal (y i) :=
  dot_unit i y

/-- Two binary databases with equal answers to every dot-product query are equal. -/
theorem parityAnswers_determine_database {n : ℕ} (y y' : DbVec n)
    (h : ∀ x, parityAnswer x y = parityAnswer x y') : y = y' :=
  parity_answers_determine y y' h

/-- Two binary databases with equal parity signs for every dot-product query are equal. -/
theorem parityPhases_determine_database {n : ℕ} (y y' : DbVec n)
    (h : ∀ x, signOfParity (parityAnswer x y) = signOfParity (parityAnswer x y')) :
    y = y' :=
  sign_answers_determine y y' h

/-- The Bernstein–Vazirani character bit is true exactly when the binary dot product is odd. -/
theorem bvCharBit_eq_true_iff {n : ℕ} (k x : Reg n) :
    bvCharBit k x = true ↔ dot x k % 2 = 1 := by
  unfold bvCharBit
  rw [decide_eq_true_iff, dot_eq_filter_card]

/-- The parity sign of the dot product equals the phase selected by the Bernstein–Vazirani
character bit. -/
theorem signOfParity_dot_eq_bvCharBit_phase {n : ℕ} (k x : Reg n) :
    signOfParity (dot x k) =
      if bvCharBit k x then (-1 : ℂ) else 1 := by
  rw [dot_eq_filter_card]
  unfold signOfParity bvCharBit
  have hm := Nat.mod_lt (Finset.univ.filter fun i => k i && x i).card
    (by omega : 0 < 2)
  interval_cases h : (Finset.univ.filter fun i => k i && x i).card % 2 <;>
    simp

/-- The Bernstein–Vazirani circuit recovers the hidden binary vector exactly and uses one oracle
query. -/
theorem singleQuery_recovery {n : ℕ} (k : Reg n) :
    Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
        (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket k) Minus ∧
      QueryCount (bvOneCallCircuit n) = 1 :=
  Qatlib.Papers.QComplexity97.XorSeparation.bv_one_query_recovery n k

/-- One oracle query recovers the hidden binary vector exactly, and that vector is uniquely
determined by all its dot-product answers, as in [TerhalSmolin1998]. -/
theorem singleQuery_recovers_unique_database {n : ℕ} (k : Reg n) :
    (Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
        (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket k) Minus ∧
      QueryCount (bvOneCallCircuit n) = 1) ∧
    (∀ y : Reg n, (∀ x : Reg n, parityAnswer x y = parityAnswer x k) → y = k) :=
  ⟨singleQuery_recovery k, fun y hy => parityAnswers_determine_database y k hy⟩

end Qatlib.Papers.SingleQuery97.MainResults.ParityRecovery
