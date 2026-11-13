/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.SubsetQueryHybrid
import Qatlib.Concepts.SearchStopping.QueryLowerBound.FamilyQueryLowerBound

/-!
# Statement of the corrected multiple-target query bound

Defines `Theorem8Corrected` for query evolutions indexed by marked subsets of fixed positive
cardinality `t`. Average success at least one half forces a floor lower bound involving the
square root of the natural quotient `Fintype.card Y / t`. For the quantum-search analysis, see
[BoyerEtAl1998].

## Main statements

* `Theorem8Corrected`: The proposition that normalized subset-indexed evolutions with off-subset
  agreement and average success at least one half require `r ≥ ⌊Real.sin (Real.pi / 8) *
  Real.sqrt (Fintype.card Y / t : ℕ)⌋` when `0 < t ≤ Fintype.card Y`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators
universe u v

/-- The proposition that normalized subset-indexed evolutions with off-subset agreement and
average success at least one half require `r ≥ ⌊Real.sin (Real.pi / 8) * Real.sqrt
(Fintype.card Y / t : ℕ)⌋` when `0 < t ≤ Fintype.card Y`. -/
def Theorem8Corrected : Prop :=
  ∀ {C : Type u} {Y : Type v} [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
    (t : ℕ), 0 < t → t ≤ Fintype.card Y →
    ∀ (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : MarkedSubsets Y t → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (f : ℕ → C → Option Y) (ψ : EuclideanSpace ℂ C), ‖ψ‖ = 1 → ∀ r : ℕ,
    (∀ A n, n < r → ∀ c, c ∉ SubsetQuerySet (f n) A.val →
      V A n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1)) →
    (Fintype.card (MarkedSubsets Y t) : ℝ) / 2 ≤
      (∑ A : MarkedSubsets Y t,
        ‖QueryProjection (SubsetQuerySet (f r) A.val) (UnitaryEvolution (V A) ψ r)‖ ^ 2) →
    ⌊Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card Y / t : ℕ)⌋ ≤ (r : ℤ)

end Qatlib.Concepts.SearchStopping.QueryLowerBound
