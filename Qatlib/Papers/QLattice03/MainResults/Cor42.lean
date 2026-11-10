/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.MatchingDefs
set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

def subsetSum_solver_fraction_bound
    (S : SubsetSumRoutine) (r : ℕ → ℕ) (hr : ∀ N, 8 * N < 2 ^ (r N))
    (δ : ℕ → ℝ) (cs : ℝ) (hcs : 0 < cs)
    (hδ : ∀ N : ℕ, 1 / (Real.log (N : ℝ)) ^ cs ≤ δ N)
    (hfrac : ∀ (N : ℕ) [NeZero N],
      δ N * (legalCard N (r N) : ℝ) ≤ (solvedCard S N (r N) : ℝ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N],
    c / (Real.log (N : ℝ)) ^ cs ≤
      (((Finset.univ.filter (fun A : Fin (r N) → ZMod N =>
          (N : ℝ) / (4 * (Real.log (N : ℝ)) ^ cs) ≤
            ((successSet S N (r N) A).card : ℝ))).card : ℝ) /
        (Fintype.card (Fin (r N) → ZMod N) : ℝ))

end Qatlib.Papers.QLattice03.MainResults
