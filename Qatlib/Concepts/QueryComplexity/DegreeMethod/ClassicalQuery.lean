/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Classical Boolean query trees

This module defines `BoolQueryTree`, a finite deterministic decision tree with Boolean oracle
answers, together with its execution and maximum query count. Distributions over such trees
model randomized query programs through success probabilities and expected query costs. The
deterministic query model provides the classical comparison for the polynomial method
[BealsEtAl2001].

## Main statements

* `BoolQueryTree.Run`: executes a tree and returns its output and query count.
* `BoolQueryTree.run_queries_le`: the execution count is bounded by `MaxQueries`.
* `BoolQueryTree.SuccessProb`: measures success for a distribution of trees.
* `BoolQueryTree.ExpectedQueries`: measures the expected number of oracle queries.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped ENNReal

/-- A finite Boolean oracle decision tree with terminal outputs and query nodes having false and
true branches. -/
inductive BoolQueryTree (Query Output : Type*) where
  | halt : Output → BoolQueryTree Query Output
  | ask : Query → BoolQueryTree Query Output → BoolQueryTree Query Output →
      BoolQueryTree Query Output

namespace BoolQueryTree

variable {Query Output : Type*}

/-- Execution of a decision tree against a Boolean oracle, returning the output and the number
of queries made. -/
def Run (oracle : Query → Bool) : BoolQueryTree Query Output → Output × ℕ
  | .halt result => (result, 0)
  | .ask query onFalse onTrue =>
      let result := if oracle query then Run oracle onTrue else Run oracle onFalse
      (result.1, result.2 + 1)

/-- The largest number of queries along any branch of a decision tree. -/
def MaxQueries : BoolQueryTree Query Output → ℕ
  | .halt _ => 0
  | .ask _ onFalse onTrue => 1 + max (MaxQueries onFalse) (MaxQueries onTrue)

/-- The number of queries made by an execution is at most the maximum branch query count. -/
theorem run_queries_le (oracle : Query → Bool) (tree : BoolQueryTree Query Output) :
    (Run oracle tree).2 ≤ MaxQueries tree := by
  induction tree with
  | halt result => simp [Run, MaxQueries]
  | ask query onFalse onTrue ihFalse ihTrue =>
    simp only [Run, MaxQueries]
    split <;> simp_all <;> omega

/-- The extended nonnegative success probability of a randomized decision tree program against a
fixed Boolean oracle. -/
noncomputable def SuccessProb (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) (success : Output → Prop) : ℝ≥0∞ := by
  classical
  exact ∑' tree, program tree * if success (Run oracle tree).1 then 1 else 0

/-- The extended nonnegative expected query count of a randomized decision tree program against
a fixed oracle. -/
noncomputable def ExpectedQueries (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) : ℝ≥0∞ :=
  ∑' tree, program tree * (Run oracle tree).2

/-- The condition that every tree with nonzero program mass has maximum query count at most
`bound`. -/
def BoundedQueries (program : PMF (BoolQueryTree Query Output)) (bound : ℕ) : Prop :=
  ∀ tree, program tree ≠ 0 → MaxQueries tree ≤ bound

end BoolQueryTree
end Qatlib.Concepts.QueryComplexity.DegreeMethod
