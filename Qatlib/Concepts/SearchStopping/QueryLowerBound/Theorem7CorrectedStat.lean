/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.FixedQueryLowerBound

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators
universe u v

def Theorem7Corrected : Prop :=
  ∀ {C : Type u} {Y : Type v} [Fintype C] [DecidableEq C]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : Y → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (f : ℕ → C → Option Y) (ψ : EuclideanSpace ℂ C), ‖ψ‖ = 1 → ∀ r : ℕ,
    (∀ y n, n < r → ∀ c, f n c ≠ some y →
      V y n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1)) →
    (Fintype.card Y : ℝ) / 2 ≤
      (∑ y : Y, QuerySuccess (f r) (UnitaryEvolution (V y) ψ r) y) →
    ⌊Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card Y)⌋ ≤ (r : ℤ)

end Qatlib.Concepts.SearchStopping.QueryLowerBound
