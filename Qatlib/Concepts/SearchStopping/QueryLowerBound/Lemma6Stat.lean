/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.QueryHybrid

/-!
# Statement of the quantum search hybrid estimates

Defines `Lemma6`, combining the telescoping hybrid distance bound, a final projection-distance
lower bound, and the summed quadratic deficit estimate. Its hypotheses compare normalized
evolutions whose steps agree away from the relevant labeled query fibers. For the quantum-search
analysis, see [BoyerEtAl1998].

## Main statements

* `Lemma6`: The proposition asserting the individual hybrid distance bound, the
  projection-deficit lower bound on squared state distance, and the summed `2 * r ^ 2` bound for
  labeled query evolutions.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators
universe u v

/-- The proposition asserting the individual hybrid distance bound, the projection-deficit lower
bound on squared state distance, and the summed `2 * r ^ 2` bound for labeled query
evolutions. -/
def Lemma6 : Prop :=
  ∀ {C : Type u} {Y : Type v} [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
    (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : Y → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (f : ℕ → C → Option Y) (ψ : EuclideanSpace ℂ C), ‖ψ‖ = 1 → ∀ r : ℕ,
    (∀ y n, n < r → ∀ c, f n c ≠ some y →
      V y n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1)) →
    (∀ y : Y, ‖UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r‖ ≤
      2 * ∑ i ∈ Finset.range r,
        ‖QueryProjection (Finset.univ.filter (fun c => f i c = some y))
          (UnitaryEvolution U ψ i)‖) ∧
    (∀ y : Y, 2 * (1 -
      ‖QueryProjection (Finset.univ.filter (fun c => f r c = some y))
        (UnitaryEvolution U ψ r)‖ -
      ‖QueryProjection (Finset.univ.filter (fun c => f r c = some y))ᶜ
        (UnitaryEvolution (V y) ψ r)‖) ≤
          ‖UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r‖ ^ 2) ∧
    (Fintype.card Y : ℝ) - Real.sqrt (Fintype.card Y) -
      (∑ y : Y, ‖QueryProjection (Finset.univ.filter (fun c => f r c = some y))ᶜ
        (UnitaryEvolution (V y) ψ r)‖) ≤ 2 * (r : ℝ) ^ 2

end Qatlib.Concepts.SearchStopping.QueryLowerBound
