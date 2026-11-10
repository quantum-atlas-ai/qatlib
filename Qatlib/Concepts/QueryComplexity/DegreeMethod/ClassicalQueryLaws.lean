/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

section
open scoped ENNReal
variable {Query Output : Type*}

noncomputable def runLaw (program : PMF (BoolQueryTree Query Output)) (oracle : Query → Bool) :
    CostedLaw Output := program.map (Run oracle)

@[simp] theorem runLaw_expectedCost (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runLaw program oracle) = ExpectedQueries program oracle := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost, runLaw,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  rfl

@[simp] theorem runLaw_success (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) (success : Output → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runLaw program oracle) (fun x => success x.1) =
      SuccessProb program oracle success := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, runLaw,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  rfl

theorem runLaw_bounded {program : PMF (BoolQueryTree Query Output)} {bound : ℕ}
    (h : BoundedQueries program bound) (oracle : Query → Bool) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (runLaw program oracle) bound := by
  intro x hx
  obtain ⟨tree, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact (run_queries_le oracle tree).trans (h tree ((PMF.mem_support_iff program tree).mp ht))

theorem expectedQueries_le_of_bounded {program : PMF (BoolQueryTree Query Output)} {bound : ℕ}
    (h : BoundedQueries program bound) (oracle : Query → Bool) :
    ExpectedQueries program oracle ≤ (bound : ℝ≥0∞) := by
  rw [← runLaw_expectedCost]
  exact (runLaw_bounded h oracle).expectedCost_le

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
