/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs

/-!
# Statement of the right posterior ratio bound

`BayesTruthRatioCrossingRight` states a finite run ratio bound for the truth driven learner with
absorption at a right ratio crossing. For `j < k < i`, the bound scales the initial ratio `a₀ i
/ a₀ k` by `1 / R`, under the noise and positive prior hypotheses used in the adaptive learning
analysis of [BenOrHassidim2007]

## Main statements

* `BayesTruthRatioCrossingRight`: specifies the right crossing probability bound for every
  finite fuel.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal BigOperators Classical

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition that for `j < k < i`, `1 / 2 < p < 1`, positive `R`, and a positive prior of
mass at most one, every finite absorbing run has probability at most `ENNReal.ofReal ((a₀ i
/ a₀ k) / R)` of `R * a k ≤ a i`. -/
def BayesTruthRatioCrossingRight : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (j k i : Fin n) (p ε R : ℝ) (a₀ : Fin n → ℝ),
    (j : ℕ) < (k : ℕ) → (k : ℕ) < (i : ℕ) →
    1 / 2 < p → p < 1 → 0 < R →
    (∀ m, 0 < a₀ m) → (∑ m, a₀ m) ≤ 1 →
      ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (crossingAbsorbNext hn j p ε R i k) fuel (Sum.inr a₀))
            (fun x => R * (configPosterior x.1) k ≤ (configPosterior x.1) i) ≤
          ENNReal.ofReal ((a₀ i / a₀ k) / R)

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
