/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.LearnerCutBridgeStat
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma21RestrictedQuan
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Balanced cuts for the Bayesian learner

This module proves `learnerCutBridge_answer`, connecting the prefix threshold lemma with the
learner's chosen cut in the ordered search framework of [BenOrHassidim2007]. For a strictly
positive normalized prior with no mass reaching ε, the cut set is nonempty, `stageTwoCut` has
prefix mass in [1/2 - ε, 1/2), and both posterior updates sum to one under the contract's
parameter bounds.

## Main statements

* `learnerCutBridge_answer`: the learner satisfies `LearnerCutBridge`.

## References

* [Ben-Or and Hassidim, Lemma 2.1][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- Proves `LearnerCutBridge`: under its prior and parameter hypotheses, the selected cut has
prefix mass in [1/2 - ε, 1/2), the cut set is nonempty, and both posterior updates are
normalized [BenOrHassidim2007]. -/
theorem learnerCutBridge_answer : LearnerCutBridge := by
  intro n hn a p ε hp hp1 hε hcap ha hsum hrun
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 1 ≤ Real.log n / Real.log 2 := by
    apply (one_le_div hlog2).2
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hL0 : 0 < Real.log n / Real.log 2 := by linarith
  have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ 1 / (24 * (Real.log n / Real.log 2)))
  have hcap24 : 1 / (24 * (Real.log n / Real.log 2)) ≤ (1 / 24 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 24 * (Real.log n / Real.log 2))).2
    nlinarith
  have hεhalf : ε ≤ 1 / 2 := by
    nlinarith [Real.sqrt_nonneg (1 / (24 * (Real.log n / Real.log 2)))]
  have hsmall : ∀ m, a m < ε := by
    intro m
    exact lt_of_not_ge (fun hm => hrun ⟨m, hm⟩)
  obtain ⟨k, hk0, hkn, hband⟩ := zoo_bayes_prefix_mass_threshold n a ε hε hεhalf
    (fun m => (ha m).le) hsum hsmall
  let i : Fin n := ⟨k - 1, by omega⟩
  have hprefix : prefixMass a i = ∑ j : Fin n, if j.val < k then a j else 0 := by
    apply Finset.sum_congr rfl
    intro j _hj
    have hj : (j.val ≤ i.val) = (j.val < k) := by
      apply propext
      dsimp only [i]
      omega
    simp only [hj]
  have hne : (cutSet a ε).Nonempty := by
    refine ⟨i, ?_⟩
    simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [hprefix] using hband
  have hcut : stageTwoCut (lt_of_lt_of_le zero_lt_two hn) a ε ∈ cutSet a ε := by
    simp only [stageTwoCut, dif_pos hne]
    exact Finset.min'_mem _ hne
  have hcutband := (Finset.mem_filter.mp hcut).2
  have hinv := zoo_bayes_posterior_invariants a
    (stageTwoCut (lt_of_lt_of_le zero_lt_two hn) a ε) p (fun m => (ha m).le) hsum hp hp1
  exact ⟨hne, hcutband, hinv.2.2.2, hinv.2.1⟩

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
