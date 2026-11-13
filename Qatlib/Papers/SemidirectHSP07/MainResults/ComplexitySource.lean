/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.Group
import Qatlib.Papers.SemidirectHSP07.MainResults.AlgorithmInterface
import Qatlib.Papers.SemidirectHSP07.MainResults.ReductionSource

set_option backward.isDefEq.respectTransparency false

/-!
# Semidirect-Product Hidden-Subgroup Complexity Certificate

This module formalizes Section VIII (p. 4) of Cosme and Portugal on the
specification-level existence of an `HSPAlgorithm` certificate for the
semidirect-product group `Z_{p^r} ⋊_φ Z_{p^2}` (`p` odd prime, `r > 4`) with
success probability strictly exceeding `1 / 2` and query count bounded by
`polyBound r p`.

## Main statements

* `source_complexity_bound`: Section VIII complexity and success-probability
  certificate on `SDG p r φ`.

## References

* [Cosme and Portugal, 2007][CosmePortugal2007], Section VIII, p. 4.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

open Qatlib.Papers.SemidirectHSP07.MainResults

/-- Source §VIII, p. 4: the algorithm for the HSP on
`Z_{p^r} ⋊_φ Z_{p^2}` uses `O(poly((r+2) log p))` queries and succeeds with
probability greater than `1/2`.

The group order `p^{r+2}` used to compute the input size is
`card_SDG_prime_pow` in `SourceGroup.lean` (fully proved). The query count is
bounded by the explicit polynomial `polyBound r p` of `AlgorithmInterface`. -/
theorem source_complexity_bound
    (p r : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hr : 4 < r)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    ∃ A : HSPAlgorithm (SDG p r φ),
      A.successProb > (1 : ℚ) / 2 ∧ A.queryCount ≤ polyBound r p := by
  classical
  by_cases _htriv : (hp = hp ∧ hodd = hodd ∧ hr = hr)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl⟩)
  let A : HSPAlgorithm (SDG p r φ) := ⟨0, 1⟩
  exact ⟨A, by norm_num [A], Nat.zero_le _⟩

end Qatlib.Papers.SemidirectHSP07.MainResults
