/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.MatchingDefs

/-!
# Specification of many pairs with a common gap

The proposition `exists_pair_gap` specifies a multiple of `q` between `q` and `s * q` having
many ordered pairs inside `T`. The parameters include a density condition on `T` and the bound
`8 * s * q < N`. See [Regev2004] for the paper context.

## Main statements

* `exists_pair_gap`: The proposition that some residue `q′ = k * q` with `1 ≤ k ≤ s` has at
  least `N / (32 * s³)` pairs represented by elements `t ∈ T` with `t + q′ ∈ T`, expressed as an
  integer cardinality inequality.

## References

* [Regev, 2004][Regev2004]
-/

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

/-- The proposition that some residue `q′ = k * q` with `1 ≤ k ≤ s` has at least `N / (32 * s³)`
pairs represented by elements `t ∈ T` with `t + q′ ∈ T`, expressed as an integer cardinality
inequality. -/
def exists_pair_gap (N s q : ℕ) [NeZero N] (T : Finset (ZMod N))
    (hs : 0 < s) (hq : 0 < q)
    (hsize : (N : ℤ) < (s : ℤ) * (T.card : ℤ))
    (hqN : 8 * s * q < N) : Prop :=
  ∃ q' ∈ (Finset.Icc 1 s).image (fun k : ℕ => (k * q : ZMod N)),
    (T.filter (fun t => t + q' ∈ T)).card * 32 * s ^ 3 ≥ N

end Qatlib.Papers.QLattice03.MainResults
