/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyMethod01.MajorityBounds.MajorityExactQuery.Basic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.MajorityBounds

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction
open Qatlib.Concepts.QueryComplexity.Amplification
open scoped Classical BigOperators

theorem majorityValue_eq_MajorityBit (k : ℕ) (x : Fin (k + k + 1) → Bool) :
    majorityValue (n := k + k + 1) x = MajorityBit (k := k + k + 1) x := by
  classical
  have hk : (k + k + 1) / 2 = k := by omega
  have hiff : (k + k + 1 < 2 * (Finset.univ.filter (fun i => x i = true)).card)
      ↔ (k < (Finset.univ.filter (fun i => x i = true)).card) := by omega
  simp only [majorityValue, MajorityBit, MajorityCount, hk, hiff]

theorem majorityValue_funext (k : ℕ) :
    (@MajorityBit (k + k + 1)) = majorityValue (n := k + k + 1) :=
  funext fun x => (majorityValue_eq_MajorityBit k x).symm

theorem majority_exactMinimum_lower_sharp (k : ℕ) :
    k + 1 ≤ exactMinimum (majorityValue (n := k + k + 1)) := by
  have h := (majority_minima_lower k).2.2
  rwa [majorityValue_funext k] at h

theorem majority_zeroErrorMinimum_lower_sharp (k : ℕ) (strict : Bool) :
    k + 1 ≤ zeroErrorMinimum strict (majorityValue (n := k + k + 1)) := by
  have h := majority_minima_lower k
  cases strict
  · simpa [majorityValue_funext k] using! h.1
  · simpa [majorityValue_funext k] using! h.2.1

theorem majority_exactMinimum_theta_sharp (k : ℕ) :
    k + 1 ≤ exactMinimum (majorityValue (n := k + k + 1)) ∧
      exactMinimum (majorityValue (n := k + k + 1)) ≤ k + k + 1 :=
  ⟨majority_exactMinimum_lower_sharp k, majority_exactMinimum_upper (k + k + 1)⟩

theorem majority_zeroErrorMinimum_theta_sharp (k : ℕ) (strict : Bool) :
    k + 1 ≤ zeroErrorMinimum strict (majorityValue (n := k + k + 1)) ∧
      zeroErrorMinimum strict (majorityValue (n := k + k + 1)) ≤ k + k + 1 :=
  ⟨majority_zeroErrorMinimum_lower_sharp k strict, by
    have horder := zeroError_minima_order (majorityValue (n := k + k + 1))
    cases strict
    · exact horder.1.trans (horder.2.trans (majority_exactMinimum_upper (k + k + 1)))
    · exact horder.2.trans (majority_exactMinimum_upper (k + k + 1))⟩

end Qatlib.Papers.PolyMethod01.MajorityBounds
