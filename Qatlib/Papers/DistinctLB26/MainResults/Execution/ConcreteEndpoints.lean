/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.BornSuccess

@[expose] public section

/-!
# Concrete zero-query endpoint for binary labels

The paper's asymptotic `k`-Distinctness lower bound still needs its knowledge-system
anti-concentration argument. This file records a genuine finite endpoint that the
executed query model already proves: with one binary input coordinate and no oracle
queries, the uniform average success of any fixed output rule is exactly one half.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

/-- A no-query word in the smallest nontrivial input alphabet. -/
def binaryNoQuery : List (Instr 1 2 PUnit) := []

/-- Every fixed output rule has one successful binary input at each work coordinate. -/
theorem binary_no_query_average (φ : Local 1 2 PUnit) (hφ : ‖φ‖ = 1)
    (answer : Work 1 2 PUnit → Label 1 2) :
    averageSuccess (fun x a => x = answer a) binaryNoQuery φ = (1 / 2 : ℝ) := by
  let : ∀ x : Label 1 2, DecidablePred (fun a : Work 1 2 PUnit => x = answer a) :=
    fun _ _ => Classical.propDecidable _
  unfold binaryNoQuery averageSuccess physicalSuccess
  rw [show Fintype.card (Label 1 2) = 2 by decide]
  simp only [inputRun]
  rw [Finset.sum_comm]
  have hsum (a : Work 1 2 PUnit) :
      (∑ x : Label 1 2, if x = answer a then ‖φ a‖ ^ 2 else 0) = ‖φ a‖ ^ 2 := by
    rw [Fintype.sum_eq_single (answer a)]
    · simp
    · intro b hba
      simp [hba]
  calc
    _ = (2 : ℝ)⁻¹ * ∑ a : Work 1 2 PUnit, ‖φ a‖ ^ 2 := by
      congr 1
      exact Finset.sum_congr rfl (fun a _ => hsum a)
    _ = _ := by
      rw [← EuclideanSpace.norm_sq_eq, hφ]
      norm_num

end Qatlib.Papers.DistinctLB26.MainResults.Execution
