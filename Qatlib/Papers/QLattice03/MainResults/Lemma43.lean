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

def exists_pair_gap (N s q : ℕ) [NeZero N] (T : Finset (ZMod N))
    (hs : 0 < s) (hq : 0 < q)
    (hsize : (N : ℤ) < (s : ℤ) * (T.card : ℤ))
    (hqN : 8 * s * q < N) : Prop :=
  ∃ q' ∈ (Finset.Icc 1 s).image (fun k : ℕ => (k * q : ZMod N)),
    (T.filter (fun t => t + q' ∈ T)).card * 32 * s ^ 3 ≥ N

end Qatlib.Papers.QLattice03.MainResults
