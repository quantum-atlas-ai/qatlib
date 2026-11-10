/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped ENNReal

inductive BoolQueryTree (Query Output : Type*) where
  | halt : Output → BoolQueryTree Query Output
  | ask : Query → BoolQueryTree Query Output → BoolQueryTree Query Output →
      BoolQueryTree Query Output

namespace BoolQueryTree

variable {Query Output : Type*}

def Run (oracle : Query → Bool) : BoolQueryTree Query Output → Output × ℕ
  | .halt result => (result, 0)
  | .ask query onFalse onTrue =>
      let result := if oracle query then Run oracle onTrue else Run oracle onFalse
      (result.1, result.2 + 1)

def MaxQueries : BoolQueryTree Query Output → ℕ
  | .halt _ => 0
  | .ask _ onFalse onTrue => 1 + max (MaxQueries onFalse) (MaxQueries onTrue)

theorem run_queries_le (oracle : Query → Bool) (tree : BoolQueryTree Query Output) :
    (Run oracle tree).2 ≤ MaxQueries tree := by
  induction tree with
  | halt result => simp [Run, MaxQueries]
  | ask query onFalse onTrue ihFalse ihTrue =>
    simp only [Run, MaxQueries]
    split <;> simp_all <;> omega

noncomputable def SuccessProb (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) (success : Output → Prop) : ℝ≥0∞ := by
  classical
  exact ∑' tree, program tree * if success (Run oracle tree).1 then 1 else 0

noncomputable def ExpectedQueries (program : PMF (BoolQueryTree Query Output))
    (oracle : Query → Bool) : ℝ≥0∞ :=
  ∑' tree, program tree * (Run oracle tree).2

def BoundedQueries (program : PMF (BoolQueryTree Query Output)) (bound : ℕ) : Prop :=
  ∀ tree, program tree ≠ 0 → MaxQueries tree ≤ bound

end BoolQueryTree
end Qatlib.Concepts.QueryComplexity.DegreeMethod
