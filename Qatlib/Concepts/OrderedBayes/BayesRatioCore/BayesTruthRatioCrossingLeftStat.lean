/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs

/-!
# Statement of the left posterior ratio bound

`BayesTruthRatioCrossingLeft` states a finite run ratio bound for the truth driven learner with
absorption at a left ratio crossing. For `k < i < j`, the bound scales the initial ratio `a₀ k /
a₀ i` by `1 / R`, under the noise and positive prior hypotheses used in the adaptive learning
analysis of [BenOrHassidim2007]

## Main statements

* `BayesTruthRatioCrossingLeft`: specifies the left crossing probability bound for every finite
  fuel.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal BigOperators Classical

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition that for `k < i < j`, `1 / 2 < p < 1`, positive `R`, and a positive prior of
mass at most one, every finite absorbing run has probability at most `ENNReal.ofReal ((a₀ k
/ a₀ i) / R)` of `R * a i ≤ a k`. -/
def BayesTruthRatioCrossingLeft : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (k i j : Fin n) (p ε R : ℝ) (a₀ : Fin n → ℝ),
    (k : ℕ) < (i : ℕ) → (i : ℕ) < (j : ℕ) →
    1 / 2 < p → p < 1 → 0 < R →
    (∀ m, 0 < a₀ m) → (∑ m, a₀ m) ≤ 1 →
      ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (crossingAbsorbNext hn j p ε R k i) fuel (Sum.inr a₀))
            (fun x => R * (configPosterior x.1) i ≤ (configPosterior x.1) k) ≤
          ENNReal.ofReal ((a₀ k / a₀ i) / R)

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
