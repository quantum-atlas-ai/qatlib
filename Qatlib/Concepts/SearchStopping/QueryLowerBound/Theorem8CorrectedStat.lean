/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.SubsetQueryHybrid
import Qatlib.Concepts.SearchStopping.QueryLowerBound.FamilyQueryLowerBound
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators
universe u v

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
