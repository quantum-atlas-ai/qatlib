/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.WeightedCost.ComputedBound
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BudgetPrefix
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess

def badIndicator (tr : Trace) : ℝ := if tr.oracleBad then 1 else 0

def rowBadMean (rows : (r : ℕ) → Row r) (r : ℕ) : ℝ :=
  ∑ a, ((rows r).law a).toReal * (if (rows r).bad a then 1 else 0)

theorem descend_bad_bound (rows : (r : ℕ) → Row r) (ε : ℝ) (hε : 0≤ε)
    (hrow : ∀ r,rowBadMean rows r≤ε) (r : ℕ) :
    (descend rows r).mean badIndicator≤(r:ℝ)*ε := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [descend,Tree.mean,badIndicator]
    | succ r =>
      rw [descend]
      change (∑ a, ((rows r).law a).toReal *
        ((descend rows ((rows r).next a).val).map _).mean badIndicator) ≤ _
      have hbranch (a : Fin (rows r).outcomes) :
          ((descend rows ((rows r).next a).val).map
            (prepend (r+1) ((rows r).charge a) ((rows r).bad a) a.val)).mean
            badIndicator ≤
          (if (rows r).bad a then 1 else 0)+(r:ℝ)*ε := by
        rw [Tree.mean_map]
        calc
          _ ≤ (descend rows ((rows r).next a).val).mean
              (fun tr : Trace => (if (rows r).bad a then 1 else 0)+badIndicator tr) := by
            apply Tree.mean_mono
            apply Tree.all_of_forall
            intro tr
            cases hb : (rows r).bad a <;> cases ht : tr.oracleBad <;> simp [prepend,badIndicator,ht]
          _ = (if (rows r).bad a then 1 else 0)+
              (descend rows ((rows r).next a).val).mean badIndicator := by
            rw [Tree.mean_add,Tree.mean_const]
          _ ≤ _ := by
            apply add_le_add (le_refl _)
            exact (ih _ ((rows r).next a).isLt).trans
              (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt_succ ((rows r).next a).isLt)) hε)
      calc
        _ ≤ ∑ a, ((rows r).law a).toReal * ((if (rows r).bad a then 1 else 0)+(r:ℝ)*ε) :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hbranch a) ENNReal.toReal_nonneg)
        _ = rowBadMean rows r+(r:ℝ)*ε := by
          simp only [rowBadMean,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,Tree.weights_sum,one_mul]
        _ ≤ _ := by have h:=hrow r; push_cast; nlinarith

theorem initialized_bad_bound {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (ε : ℝ) (hε : 0≤ε) (hrow : ∀ r,rowBadMean rows r≤ε) :
    (initialized p rows).mean badIndicator≤(L:ℝ)*ε := by
  change (∑ i : Fin L, (p i).toReal*(descend rows i.val).mean badIndicator) ≤ _
  calc
    _ ≤ ∑ i : Fin L, (p i).toReal*((L:ℝ)*ε) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact (descend_bad_bound rows ε hε hrow i.val).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le) hε)
    _ = _ := by rw [← Finset.sum_mul,Tree.weights_sum,one_mul]

theorem bad_probability (t : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace) :
    t.probability (fun tr => tr.oracleBad=true)=t.mean badIndicator := by
  apply Tree.mean_congr
  apply Tree.all_of_forall
  intro tr
  cases h : tr.oracleBad <;> simp [badIndicator,h]
end Qatlib.Papers.QAOAScaling23.BudgetPrefix
