/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.BvParityBound.ParityAverageSuccessBoundStat
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

/-!
# Average classical success for parity-secret recovery

This module proves the aggregate success bound for randomized adaptive Boolean query trees
recovering a parity secret. A single probability distribution on trees with at most `T` queries
has success probabilities, summed over all secrets, at most `2 ^ T`; the counting argument
complements the oracle separation of [BernsteinVazirani1997].

## Main statements

* `parityAverageSuccessBound`: establishes `ParityAverageSuccessBound` for every input length
  and query bound.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

namespace Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib
open scoped BigOperators ENNReal

/-- A deterministic Boolean query tree correctly recovers at most `2 ^ MaxQueries τ` parity
secrets, expressed as a sum in the extended nonnegative reals. -/
private theorem bv_correct_secret_count (n : ℕ) (τ : BoolQueryTree (Reg n) (Reg n)) :
    (∑ k : Reg n, if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (bvCharBit k) τ).1 = k then (1 : ℝ≥0∞) else 0) ≤
      ((2 ^ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries τ : ℕ) : ℝ≥0∞) := by
  classical
  let S :=
      Finset.univ.filter
      (fun k : Reg n => (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (bvCharBit k) τ).1 = k)
  have hsub : S ⊆ bvTreeOutputs τ := by
    intro k hk
    have he := (Finset.mem_filter.mp hk).2
    rw [← he]
    exact bv_run_mem_outputs (bvCharBit k) τ
  have hc := (Finset.card_le_card hsub).trans (bv_output_count_le τ)
  have he : (∑ k : Reg n, if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (bvCharBit k) τ).1 = k
      then (1 : ℝ≥0∞) else 0) = (S.card : ℝ≥0∞) := by simp [S]
  rw [he]
  exact_mod_cast hc

/-- For any probability distribution on Boolean query trees with at most `T` queries, the real
success probabilities of recovering parity secrets sum to at most `2 ^ T` over all secrets. -/
theorem parityAverageSuccessBound : ParityAverageSuccessBound := by
  classical
  intro n T P hT
  let mass (k : Reg n) :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb P (bvCharBit k)
      (fun output => output = k)
  have he : (∑ k, mass k) = ∑' τ, P τ *
      ∑ k : Reg n, if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (bvCharBit k) τ).1 = k then (1 : ℝ≥0∞) else 0 := by
    dsimp only [mass, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb]
    rw [← tsum_fintype (L := SummationFilter.unconditional (Reg n)), ENNReal.tsum_comm]
    apply tsum_congr
    intro τ
    rw [tsum_fintype, Finset.mul_sum]
    congr 2
    funext k
    congr
  have hb : (∑ k, mass k) ≤ ((2 ^ T : ℕ) : ℝ≥0∞) := by
    rw [he]
    calc
      _ ≤ ∑' τ, P τ * ((2 ^ T : ℕ) : ℝ≥0∞) := by
        apply ENNReal.tsum_le_tsum
        intro τ
        by_cases hz : P τ = 0
        · simp [hz]
        · apply mul_le_mul_right
          exact (bv_correct_secret_count n τ).trans (by
            exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (hT τ hz))
      _ = _ := by rw [ENNReal.tsum_mul_right, P.tsum_coe, one_mul]
  have hterm (k : Reg n) : mass k ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) ((Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_univ k)).trans hb)
  have hreal := ENNReal.toReal_mono (by simp : ((2 ^ T : ℕ) : ℝ≥0∞) ≠ ⊤) hb
  rw [ENNReal.toReal_sum (fun k _ => hterm k)] at hreal
  simpa only [mass, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat] using! hreal

end Qatlib.Concepts.UniformBqp.BvParityBound
