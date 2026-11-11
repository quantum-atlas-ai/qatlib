/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthRatioCrossingLeftStat

/-!
# Left posterior ratio crossing bounds

The left ratio crossing statement is proved for `k < i < j`, strictly positive initial entries
of total mass at most one, and `1 / 2 < p < 1`. The absorbing kernel has a finite run crossing
probability bounded by the initial ratio divided by `R`, with bound `1 / R` for a uniform prior,
corresponding to the ratio analysis associated with Lemma 2.5 of [BenOrHassidim2007]

## Main statements

* `zoo_bayes_truth_ratio_crossing_left`: proves the general prior crossing statement.
* `zoo_bayes_truth_ratio_crossing_left_uniform`: specializes the bound to the uniform prior.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal BigOperators NNReal

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- For `k < i < j`, `1 / 2 < p < 1`, positive `R`, and a positive prior of mass at most one,
proves the finite run absorbing crossing bound `ENNReal.ofReal ((a₀ k / a₀ i) / R)`; see
[Ben-Or and Hassidim, Lemma 2.5][BenOrHassidim2007]. -/
theorem zoo_bayes_truth_ratio_crossing_left : BayesTruthRatioCrossingLeft := by
  intro n hn k i j p ε R a₀ hki hij hp hp1 hR hpos hsum fuel
  refine le_trans (ville_event_bound (crossingAbsorbNext hn j p ε R k i)
    (ratioPotential k i)
    (fun cfg => R * configPosterior cfg i ≤ configPosterior cfg k)
    (fun cfg => truthInv (configPosterior cfg))
    (ENNReal.ofReal R)
    (ENNReal.ofReal_pos.mpr hR).ne'
    ENNReal.ofReal_ne_top
    (fun s => crossingAbsorb_one_step_left hn k i j hp hp1 hki hij s)
    (fun s hs cfg hcfg => crossingAbsorb_support_inv hn j p ε R k i hp hp1 s hs cfg hcfg)
    (fun cfg hI hQ => ENNReal.ofReal_le_ofReal
      ((le_div_iff₀ (hI.1 i)).mpr hQ))
    fuel (Sum.inr a₀) ⟨hpos, hsum⟩) ?_
  rw [show ratioPotential k i (Sum.inr a₀) / ENNReal.ofReal R
      = ENNReal.ofReal ((a₀ k / a₀ i) / R) from by
      rw [ratioPotential, configPosterior, Sum.elim_inr, id_eq, ENNReal.ofReal_div_of_pos hR]]

/-- For `k < i < j`, `1 / 2 < p < 1`, and positive `R`, the absorbing run from the uniform prior
has probability at most `ENNReal.ofReal (1 / R)` of `R * a i ≤ a k` at every fuel. -/
theorem zoo_bayes_truth_ratio_crossing_left_uniform :
    ∀ (n : ℕ) (hn : 0 < n) (k i j : Fin n) (p ε R : ℝ),
      (k : ℕ) < (i : ℕ) → (i : ℕ) < (j : ℕ) → 1 / 2 < p → p < 1 → 0 < R →
        ∀ fuel : ℕ,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (crossingAbsorbNext hn j p ε R k i) fuel
              (Sum.inr uniformPosterior))
              (fun x => R * (configPosterior x.1) i ≤ (configPosterior x.1) k) ≤
            ENNReal.ofReal (1 / R) := by
  intro n hn k i j p ε R hki hij hp hp1 hR fuel
  have hbound := zoo_bayes_truth_ratio_crossing_left n hn k i j p ε R uniformPosterior hki hij
    hp hp1 hR (fun m => div_pos zero_lt_one (by exact_mod_cast hn))
    (by
      have hnR : ((n : ℝ)) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      simp only [uniformPosterior]
      rw [← Finset.sum_div, show (∑ _m : Fin n, (1 : ℝ)) = (n : ℝ) from by simp, div_self hnR])
    fuel
  have hratio : (uniformPosterior k / uniformPosterior i : ℝ) = 1 := by
    simp only [uniformPosterior]
    exact div_self (one_div_ne_zero (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)))
  simpa [hratio] using hbound

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
