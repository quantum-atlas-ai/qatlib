/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.UniformBqp.BvParityBound

section
variable {Q O : Type} [DecidableEq O]

def bvTreeOutputs : BoolQueryTree Q O → Finset O
  | .halt o => {o}
  | .ask _ l r => bvTreeOutputs l ∪ bvTreeOutputs r

theorem bv_run_mem_outputs (f : Q → Bool) (T : BoolQueryTree Q O) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run f T).1 ∈ bvTreeOutputs T := by
  induction T with
  | halt o => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, bvTreeOutputs]
  | ask q l r hl hr =>
      cases hf : f q <;> simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run,
          bvTreeOutputs, hf, hl, hr]

theorem bv_output_count_le (T : BoolQueryTree Q O) :
    (bvTreeOutputs T).card ≤ 2 ^ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T := by
  induction T with
  | halt o => simp [bvTreeOutputs, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | ask q l r hl hr =>
      simp only [bvTreeOutputs,
          Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
      calc
        _ ≤ (bvTreeOutputs l).card + (bvTreeOutputs r).card := Finset.card_union_le _ _
        _ ≤ 2 ^ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l + 2 ^ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries r :=
          Nat.add_le_add hl hr
        _ ≤ 2 ^ max (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l) (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries r) +
            2 ^ max (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l) (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries r) := by
          exact Nat.add_le_add (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
            (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
        _ = _ := by rw [pow_add]; omega

end

theorem bv_classical_zero_error_lower_bound (n : ℕ)
    (T : BoolQueryTree (Reg n) (Reg n))
    (hT : ∀ k, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (bvCharBit k) T).1 = k) :
    n ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T := by
  have hall : Finset.univ ⊆ bvTreeOutputs T := by
    intro k _
    rw [← hT k]
    exact bv_run_mem_outputs (bvCharBit k) T
  have hc : 2 ^ n ≤ 2 ^ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T := by
    calc
      _ = Finset.card (Finset.univ : Finset (Reg n)) := by simp
      _ ≤ (bvTreeOutputs T).card := Finset.card_le_card hall
      _ ≤ _ := bv_output_count_le T
  by_contra hn
  have hl :=
      Nat.pow_lt_pow_right (by omega : 1 < 2)
      (by omega : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T < n)
  omega

end Qatlib.Concepts.UniformBqp.BvParityBound
