/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.EntropyBound
import Qatlib.Papers.SingleQuery97.MainResults.ClassicalAdaptive

/-!
# Expected classical query bounds from entropy

These results express the classical information bound using the prior expectation of the number
of queries actually executed by an exact adaptive tree. `source_information_lower_bound` handles
any finite answer alphabet of size at least two, and `coin_expected_entropy_bound` specializes
it to subset weighing. See [TerhalSmolin1998] for the source development.

## Main statements

* `source_information_lower_bound`: bounds expected queries below by prior entropy in bits
  divided by the answer capacity in bits.
* `coin_expected_entropy_bound`: uses the `n + 1` possible weighing answers.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.ClassicalEntropy

open Qatlib.Concepts.QueryComplexity.AdaptiveInfo
open ClassicalDefs EntropyBound

/-- For a nonnegative prior summing to one and a tree that exactly identifies every hidden
label, expected executed queries are at least the entropy in bits divided by `log₂
(Fintype.card A)`, when the answer alphabet has at least two elements. See
[TerhalSmolin1998]. -/
theorem source_information_lower_bound {I A Y : Type} [Fintype A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] (oracle : Y → I → A)
    (tree : QueryTree I A Y) (p : Y → ℝ)
    (hp : ∀ y, 0≤p y) (hsum : ∑ y,p y=1) (hA : 2≤Fintype.card A)
    (hcorrect : ∀ y, (run (oracle y) tree).1=y) :
    (entropy p/Real.log 2)/Real.logb 2 (Fintype.card A) ≤ expectedQueries oracle tree p :=
  EntropyBound.source_information_lower_bound oracle tree p hp hsum hA hcorrect

/-- For `n > 0` and a nonnegative prior summing to one, any exact adaptive coin-weighing tree
has expected query count at least the prior entropy in bits divided by `log₂ (n + 1)`. See
[TerhalSmolin1998]. -/
theorem coin_expected_entropy_bound (n : ℕ) (hn : 0<n)
    (tree : QueryTree (DatabaseDefs.DbVec n) (Fin (n+1)) (DatabaseDefs.DbVec n))
    (p : DatabaseDefs.DbVec n → ℝ) (hp : ∀ y, 0≤p y) (hsum : ∑ y,p y=1)
    (hcorrect : ∀ y, (run (ClassicalAdaptive.weighing y) tree).1=y) :
    (entropy p/Real.log 2)/Real.logb 2 (n+1) ≤
      expectedQueries ClassicalAdaptive.weighing tree p := by
  have h := EntropyBound.source_information_lower_bound ClassicalAdaptive.weighing tree p hp hsum
    (show 2≤Fintype.card (Fin (n+1)) by simp; omega) hcorrect
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using h

end Qatlib.Papers.SingleQuery97.MainResults.ClassicalEntropy
