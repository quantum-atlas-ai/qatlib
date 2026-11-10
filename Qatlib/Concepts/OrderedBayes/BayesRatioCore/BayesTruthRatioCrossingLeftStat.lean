/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs
set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal BigOperators Classical

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

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
