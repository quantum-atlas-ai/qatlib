/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Lemma2Restricted
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized

/-!
# A restricted randomized-search contract

This module proves `lemma2Restricted`, the restricted randomized-search contract imported from
the query lower-bound interface. The proof extracts its required conclusions from
`search_randomized_angle`.

The result supplies a restricted interface to randomized quantum search [BoyerEtAl1998].

## Main statements

* `lemma2Restricted`: Establishes `Lemma2Restricted` by extracting the required conclusions from
  the randomized search angle law [BoyerEtAl1998].

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.QueryLowerBound

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

universe u

/-- Establishes `Lemma2Restricted` by extracting the required conclusions from the randomized
search angle law [BoyerEtAl1998]. -/
theorem lemma2Restricted : Lemma2Restricted.{u} := by
  intro I _ _ hN A θ hθ h2 m hm
  have h := search_randomized_angle hN A θ hθ h2 m hm
  exact ⟨h.1, h.2.2⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
