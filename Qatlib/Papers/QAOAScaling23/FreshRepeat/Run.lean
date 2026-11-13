/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BudgetPrefix.Budget
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Confidence amplification of budgeted descent

`outerIterations` chooses the number of fresh trials from a target error. The module combines
the dyadic failure bound with the budgeted descent estimates to prove the error and total-charge
guarantees of `corrected_source_run` under the stated row-law and resource hypotheses.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `dyadic_error_bound`: For positive `δ`, the dyadic error `(1/2)^(outerIterations δ)` is at
  most `δ`.
* `corrected_source_run`: Under the stated row-law, positive-mass, row-charge, and row-failure
  hypotheses, budget `B ≥ 15 * C * M * N` with `M ≥ 1 / sqrt (popt q)` gives amplified failure
  probability at most positive `δ` and pathwise total charge at most `outerIterations δ * B`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.FreshRepeat
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
open Qatlib.Papers.QAOAScaling23.BudgetPrefix

/-- The natural ceiling of `logb 2 (1 / δ)`, used as the number of outer repetitions. -/
def outerIterations (δ : ℝ) : ℕ := Nat.ceil (Real.logb 2 (1/δ))

/-- For positive `δ`, the dyadic error `(1/2)^(outerIterations δ)` is at most `δ`. -/
theorem dyadic_error_bound (δ : ℝ) (hδ : 0<δ) :
    (1/2:ℝ)^outerIterations δ≤δ := by
  have hceil : Real.logb 2 (1/δ)≤(outerIterations δ:ℝ) := Nat.le_ceil _
  have hm : (2:ℝ)^(Real.logb 2 (1/δ))≤(2:ℝ)^((outerIterations δ:ℕ):ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<2)).2 hceil
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity),Real.rpow_natCast] at hm
  have hp : 0<(2:ℝ)^outerIterations δ := by positivity
  have hi := (inv_le_inv₀ hp (show 0<1/δ by positivity)).2 hm
  simpa only [one_div,inv_inv,inv_pow] using hi

/-- If each trial has paid charge at most `B` on every path, a batch of `k` trials has total
charge at most `k * B`. -/
theorem freshBatch_path_cap
    (trial : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace)
    (B : ℕ) (hcap : trial.All (fun tr => paid tr≤B)) (k : ℕ) :
    (freshBatch trial k).All (fun b => b.totalPaid≤k*B) := by
  induction k with
  | zero => simp [freshBatch,Tree.All]
  | succ k ih =>
    rw [freshBatch,Tree.all_bind]
    apply Tree.all_mono _ hcap
    intro tr ht
    rw [Tree.all_map]
    apply Tree.all_mono _ ih
    intro b hb
    change paid tr+b.totalPaid≤(k+1)*B
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Under the stated row-law, positive-mass, row-charge, and row-failure hypotheses, budget `B ≥
15 * C * M * N` with `M ≥ 1 / sqrt (popt q)` gives amplified failure probability at most
positive `δ` and pathwise total charge at most `outerIterations δ * B`. -/
theorem corrected_source_run {L : ℕ} (hL : 0<L) (p : PMF (Fin L)) (q : ℕ → ℝ)
    (hq : ∀ i : Fin L,(p i).toReal=q i.val) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows)
    (C N M ε δ : ℝ) (hC : 0<C) (hN : 0<N) (hδ : 0<δ)
    (hM : 1/Real.sqrt (popt q)≤M)
    (hrow : ∀ j,0<j → rowCharge rows j≤2*C*N/Real.sqrt (prefixSum q j))
    (hε : 0≤ε) (hrowBad : ∀ r,rowBadMean rows r≤ε) (hunion : (L:ℝ)*ε≤1/6)
    (B initialFee : ℕ) (hinitFee : (initialFee:ℝ)≤C*N) (hbudget : 15*C*M*N≤(B:ℝ)) :
    (freshBatch (budgetTrial p rows B initialFee) (outerIterations δ)).probability
        (fun b => b.best≠some 0)≤δ ∧
      (freshBatch (budgetTrial p rows B initialFee) (outerIterations δ)).All
        (fun b => b.totalPaid≤outerIterations δ*B) := by
  have htrial := source_budget_half_failure hL p q hq h0 hnn rows hlaw C N M ε hC hN hM
    hrow hε hrowBad hunion B initialFee hinitFee hbudget
  exact ⟨(actual_failure_le_half_power _ htrial.1 _).trans (dyadic_error_bound δ hδ),
    freshBatch_path_cap _ B htrial.2 _⟩
end Qatlib.Papers.QAOAScaling23.FreshRepeat
