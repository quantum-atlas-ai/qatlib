/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Execution laws for randomized query trees

This module packages execution of a randomized Boolean decision tree as `BoolQueryTree.runLaw`,
a joint law of output and query cost. It identifies the law with the success probability and
expected query count definitions, and transfers a uniform query bound to the expected cost.
These laws formalize the classical query model used for comparison in [BealsEtAl2001].

## Main statements

* `BoolQueryTree.runLaw_expectedCost`: expected execution cost equals `ExpectedQueries`.
* `BoolQueryTree.runLaw_success`: the output event equals `SuccessProb`.
* `BoolQueryTree.expectedQueries_le_of_bounded`: a uniform query bound also bounds the
  expectation.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

section
open scoped ENNReal
variable {Query Output : Type*}

/-- The joint output and query-cost law obtained by mapping a randomized tree program through
execution against `oracle`. -/
noncomputable def runLaw (program : PMF (BoolQueryTree Query Output)) (oracle : Query → Bool) :
    CostedLaw Output := program.map (Run oracle)

/-- The expected cost of the execution law equals the program expected query count. -/
@[simp] theorem runLaw_expectedCost (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runLaw program oracle) = ExpectedQueries program oracle := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost, runLaw,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  rfl

/-- The success event probability under the execution law equals `SuccessProb` for the same
output predicate. -/
@[simp] theorem runLaw_success (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) (success : Output → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runLaw program oracle) (fun x => success x.1) =
      SuccessProb program oracle success := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, runLaw,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  rfl

/-- A uniform bound on the maximum query counts of supported trees bounds the cost in the
execution law. -/
theorem runLaw_bounded {program : PMF (BoolQueryTree Query Output)} {bound : ℕ}
    (h : BoundedQueries program bound) (oracle : Query → Bool) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (runLaw program oracle) bound := by
  intro x hx
  obtain ⟨tree, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact (run_queries_le oracle tree).trans (h tree ((PMF.mem_support_iff program tree).mp ht))

/-- The expected query count is at most any uniform bound on the maximum query counts of
supported trees. -/
theorem expectedQueries_le_of_bounded {program : PMF (BoolQueryTree Query Output)} {bound : ℕ}
    (h : BoundedQueries program bound) (oracle : Query → Bool) :
    ExpectedQueries program oracle ≤ (bound : ℝ≥0∞) := by
  rw [← runLaw_expectedCost]
  exact (runLaw_bounded h oracle).expectedCost_le

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
