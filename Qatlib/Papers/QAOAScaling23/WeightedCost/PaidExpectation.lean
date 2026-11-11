/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.WeightedVisits
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Composition

/-!
# Visit-weighted expected descent charges

`rowCharge` assigns each rank its mean outgoing charge, and `earned` sums a reward over the
states of a trace. The expected paid charge of initialized descent is the sum of row charges
weighted by their rank-visit probabilities `q j / prefixSum q (j + 1)` under the stated row law.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `descend_paid_reward`: The mean paid charge of descent equals its mean accumulated state
  reward for reward function `rowCharge rows`.
* `initialized_paid_formula`: Under the rank-distribution and row-law hypotheses with positive
  optimal mass and nonnegative weights, initialized descent has mean paid charge equal to the
  sum of row charges times `q j / prefixSum q (j + 1)`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.WeightedCost
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess

/-- The mean outgoing row charge at rank `r + 1`, with charge zero at rank zero. -/
def rowCharge (rows : (r : ℕ) → Row r) : ℕ → ℝ
  | 0 => 0
  | r+1 => ∑ a, ((rows r).law a).toReal * ((rows r).charge a : ℝ)

/-- The sum of the state rewards `c` over all states recorded in a trace. -/
def earned (c : ℕ → ℝ) (tr : Trace) : ℝ := (tr.states.map c).sum

/-- The mean paid charge of descent equals its mean accumulated state reward for reward function
`rowCharge rows`. -/
theorem descend_paid_reward (rows : (r : ℕ) → Row r) (r : ℕ) :
    (descend rows r).mean (fun tr => (paid tr:ℝ))=
      (descend rows r).mean (earned (rowCharge rows)) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [descend,Tree.mean,paid,earned,rowCharge]
    | succ r =>
      rw [descend]
      change (∑ a, ((rows r).law a).toReal *
        ((descend rows ((rows r).next a).val).map _).mean (fun tr => (paid tr:ℝ))) = _
      have hpaid (a : Fin (rows r).outcomes) :
          ((descend rows ((rows r).next a).val).map
            (prepend (r+1) ((rows r).charge a) ((rows r).bad a) a.val)).mean (fun tr => (paid tr:ℝ)) =
          ((rows r).charge a:ℝ)+(descend rows ((rows r).next a).val).mean (earned (rowCharge rows)) := by
        rw [Tree.mean_map]
        simp only [paid,prepend,List.sum_cons,Nat.cast_add]
        rw [Tree.mean_add,Tree.mean_const]
        exact congrArg (fun x : ℝ => ((rows r).charge a:ℝ)+x) (ih _ ((rows r).next a).isLt)
      simp_rw [hpaid]
      change _ = ∑ a, ((rows r).law a).toReal *
        ((descend rows ((rows r).next a).val).map _).mean (earned (rowCharge rows))
      simp_rw [Tree.mean_map]
      simp only [earned,prepend,List.map_cons,List.sum_cons]
      simp_rw [Tree.mean_add,Tree.mean_const]
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,Tree.weights_sum,one_mul,rowCharge]
      rfl

/-- For a list of ranks below `L`, the sum of its rewards equals the sum over ranks below `L` of
each reward times its occurrence count. -/
theorem reward_count_identity (xs : List ℕ) (c : ℕ → ℝ) (L : ℕ)
    (hxs : ∀ j∈xs,j<L) :
    (xs.map c).sum=∑ j ∈ Finset.range L, c j*(xs.count j:ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x<L := hxs x (by simp)
    have ht : ∀ j∈xs,j<L := fun j hj => hxs j (by simp [hj])
    rw [List.map_cons,List.sum_cons,ih ht]
    have h (j : ℕ) : c j*((x::xs).count j:ℝ)=
        (if x=j then c j else 0)+c j*(xs.count j:ℝ) := by
      by_cases hj : x=j
      · subst j; simp [mul_add,add_comm]
      · simp [hj]
    simp_rw [h,Finset.sum_add_distrib]
    simp [hx]

/-- Under the rank-distribution and row-law hypotheses with positive optimal mass and
nonnegative weights, initialized descent has mean paid charge equal to the sum of row
charges times `q j / prefixSum q (j + 1)`. -/
theorem initialized_paid_formula {L : ℕ} (p : PMF (Fin L)) (q : ℕ → ℝ)
    (hq : ∀ i : Fin L,(p i).toReal=q i.val) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows) :
    (initialized p rows).mean (fun tr => (paid tr:ℝ))=
      ∑ j : Fin L, rowCharge rows j.val * (q j.val/prefixSum q (j.val+1)) := by
  have hcost : (initialized p rows).mean (fun tr => (paid tr:ℝ))=
      (initialized p rows).mean (earned (rowCharge rows)) := by
    unfold initialized Tree.mean
    apply Finset.sum_congr rfl
    intro i _
    rw [descend_paid_reward]
  rw [hcost]
  have hreward : (initialized p rows).mean (earned (rowCharge rows))=
      (initialized p rows).mean (fun tr => ∑ j ∈ Finset.range L, rowCharge rows j*visits j tr) := by
    apply Tree.mean_congr
    change ∀ i : Fin L, (descend rows i.val).All _
    intro i
    apply Tree.all_mono _ (descend_states_le rows i.val)
    intro tr ht
    exact reward_count_identity tr.states _ L (fun j hj => (ht j hj).trans_lt i.isLt)
  rw [hreward,Tree.mean_sum]
  simp_rw [Tree.mean_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [initialized_visit_mean p q hq h0 hnn rows hlaw j]
end Qatlib.Papers.QAOAScaling23.WeightedCost
