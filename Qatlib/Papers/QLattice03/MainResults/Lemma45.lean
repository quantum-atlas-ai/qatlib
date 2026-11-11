/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma43
import Qatlib.Papers.QLattice03.MainResults.Cor42

/-!
# Good matching existence specification

`exists_good_matching` specifies an exponent and a matching from `matchingFamily` that is both a
matching at a bounded multiple of the requested gap and good for the subset sum routine. Its
parameters record the inverse-logarithmic legal-input success assumptions. See [Regev2004] for
the paper context.

## Main statements

* `exists_good_matching`: The proposition that some integer `cm ≥ 3` with `cm > 3 * cs` yields,
  for every permitted positive `q`, a member of `matchingFamily` satisfying `IsQMatching` at a
  multiple `k * q` with `1 ≤ k ≤ logPow N cm`, and satisfying `IsGoodMatching`.

## References

* [Regev, 2004][Regev2004]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

/-- The proposition that some integer `cm ≥ 3` with `cm > 3 * cs` yields, for every permitted
positive `q`, a member of `matchingFamily` satisfying `IsQMatching` at a multiple `k * q`
with `1 ≤ k ≤ logPow N cm`, and satisfying `IsGoodMatching`. -/
def exists_good_matching
    (S : SubsetSumRoutine) (r : ℕ → ℕ) (hr : ∀ N, 8 * N < 2 ^ (r N))
    (δ : ℕ → ℝ) (cs : ℝ) (hcs : 0 < cs)
    (hδ : ∀ N : ℕ, 1 / (Real.log (N : ℝ)) ^ cs ≤ δ N)
    (hfrac : ∀ (N : ℕ) [NeZero N],
      δ N * (legalCard N (r N) : ℝ) ≤ (solvedCard S N (r N) : ℝ)) : Prop :=
  ∃ cm : ℕ, 3 ≤ cm ∧ 3 * cs < (cm : ℝ) ∧ ∀ (N : ℕ) [NeZero N] (q : ℕ),
    0 < q → 8 * q * logPow N cm < N →
      ∃ f ∈ matchingFamily N q (logPow N cm), ∃ k ∈ Finset.Icc 1 (logPow N cm),
        IsQMatching N ((k * q : ℕ) : ZMod N) f ∧ IsGoodMatching N S (r N) cm f

end Qatlib.Papers.QLattice03.MainResults
