/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Classical query lower bound for parity-secret recovery

This module counts the possible outputs of an adaptive Boolean query tree by its maximum number
of queries. Applying the count to exact recovery of every parity secret yields the deterministic
classical lower bound in the Bernstein–Vazirani setting [BernsteinVazirani1997].

## Main statements

* `bv_output_count_le`: a tree with maximum query count `T` has at most `2 ^ T` distinct
  outputs.
* `bv_classical_zero_error_lower_bound`: a tree recovering every `n`-bit secret requires at
  least `n` queries on some path.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.UniformBqp.BvParityBound

section
variable {Q O : Type} [DecidableEq O]

/-- The finite set of all output labels occurring at leaves of a Boolean query tree. -/
def bvTreeOutputs : BoolQueryTree Q O → Finset O
  | .halt o => {o}
  | .ask _ l r => bvTreeOutputs l ∪ bvTreeOutputs r

/-- The output produced by running a Boolean query tree belongs to its set `bvTreeOutputs`. -/
theorem bv_run_mem_outputs (f : Q → Bool) (T : BoolQueryTree Q O) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run f T).1 ∈ bvTreeOutputs T := by
  induction T with
  | halt o => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, bvTreeOutputs]
  | ask q l r hl hr =>
      cases hf : f q <;> simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run,
          bvTreeOutputs, hf, hl, hr]

/-- The number of distinct leaf outputs is at most two raised to the maximum query count of the
tree. -/
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

/-- A deterministic Boolean query tree that recovers every `n`-bit parity secret has maximum
query count at least `n`. -/
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
