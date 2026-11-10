/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyMethod01.MajorityBounds.MajorityExactDegree
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparison
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.MajorityBounds

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open scoped Classical BigOperators

theorem majority_exactMinimum_lower (n : ℕ) :
    n / 2 ≤ exactMinimum (majorityValue (n := n)) := by
  have h := (minimum_degree_bounds (majorityValue (n := n))).1
  rw [majority_exactDegree] at h
  omega

theorem majority_exactMinimum_upper (n : ℕ) :
    exactMinimum (majorityValue (n := n)) ≤ n :=
  (minima_upper_and_order (majorityValue (n := n))).2

theorem majority_exactMinimum_theta (n : ℕ) :
    n / 2 ≤ exactMinimum (majorityValue (n := n)) ∧
      exactMinimum (majorityValue (n := n)) ≤ n :=
  ⟨majority_exactMinimum_lower n, majority_exactMinimum_upper n⟩

theorem majority_boundedMinimum_upper (n : ℕ) :
    boundedMinimum (majorityValue (n := n)) ≤ n :=
  (minima_upper_and_order (majorityValue (n := n))).1.trans (majority_exactMinimum_upper n)

theorem majority_tree_depth_ge (n : ℕ) (t : BoolQueryTree (Fin n) Bool)
    (h : ∀ x : Fin n → Bool, (BoolQueryTree.Run (fun i => x i) t).1 = majorityValue x) :
    n ≤ t.MaxQueries := by
  have hdeg := tree_depth_ge_exactDegree (I := Fin n) t (majorityValue (n := n)) h
  rwa [majority_exactDegree] at hdeg

end Qatlib.Papers.PolyMethod01.MajorityBounds
