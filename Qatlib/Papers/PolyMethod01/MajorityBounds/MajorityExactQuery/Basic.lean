/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyMethod01.MajorityBounds.MajorityExactDegree
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparison

/-!
# Basic query bounds for strict majority

These results bound the exact query minimum of strict majority between natural-number `n / 2`
and `n`, and bound its bounded-error minimum by `n`. The deterministic comparison
`majority_tree_depth_ge` requires depth at least `n` for every correct Boolean query tree. These
results accompany the polynomial-method analysis in [BealsEtAl2001].

## Main statements

* `majority_exactMinimum_theta`: The exact query minimum for strict majority on `n` bits lies
  between natural-number `n / 2` and `n`.
* `majority_tree_depth_ge`: Every deterministic Boolean query tree computing strict majority on
  `n` bits has maximum query count at least `n`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

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

/-- The exact query minimum for strict majority on `n` bits is at least natural-number `n / 2`. -/
theorem majority_exactMinimum_lower (n : ℕ) :
    n / 2 ≤ exactMinimum (majorityValue (n := n)) := by
  have h := (minimum_degree_bounds (majorityValue (n := n))).1
  rw [majority_exactDegree] at h
  omega

/-- The exact query minimum for strict majority on `n` bits is at most `n`. -/
theorem majority_exactMinimum_upper (n : ℕ) :
    exactMinimum (majorityValue (n := n)) ≤ n :=
  (minima_upper_and_order (majorityValue (n := n))).2

/-- The exact query minimum for strict majority on `n` bits lies between natural-number `n / 2`
and `n`. -/
theorem majority_exactMinimum_theta (n : ℕ) :
    n / 2 ≤ exactMinimum (majorityValue (n := n)) ∧
      exactMinimum (majorityValue (n := n)) ≤ n :=
  ⟨majority_exactMinimum_lower n, majority_exactMinimum_upper n⟩

/-- The bounded-error query minimum for strict majority on `n` bits is at most `n`. See [Beals
et al., 2001][BealsEtAl2001]. -/
theorem majority_boundedMinimum_upper (n : ℕ) :
    boundedMinimum (majorityValue (n := n)) ≤ n :=
  (minima_upper_and_order (majorityValue (n := n))).1.trans (majority_exactMinimum_upper n)

/-- Every deterministic Boolean query tree computing strict majority on `n` bits has maximum
query count at least `n`. -/
theorem majority_tree_depth_ge (n : ℕ) (t : BoolQueryTree (Fin n) Bool)
    (h : ∀ x : Fin n → Bool, (BoolQueryTree.Run (fun i => x i) t).1 = majorityValue x) :
    n ≤ t.MaxQueries := by
  have hdeg := tree_depth_ge_exactDegree (I := Fin n) t (majorityValue (n := n)) h
  rwa [majority_exactDegree] at hdeg

end Qatlib.Papers.PolyMethod01.MajorityBounds
