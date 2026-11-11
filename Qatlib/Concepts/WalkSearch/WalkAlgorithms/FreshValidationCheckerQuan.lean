/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.FreshValidationCheckerStat
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.FreshCheckerBudget

/-!
# Fresh validation checker guarantee

This module proves `FreshValidationChecker` by combining the soundness and budget results for
`triCheckFresh`. Its failure analysis splits unsuccessful runs into noisy-search failures and
failures of amplified extraction after a vertex has been selected.

The finite-tape counting bounds yield the combined inverse-power failure estimate, while
`fresh_cost_le` supplies the cost guarantee. These are checker components for the quantum-walk
search framework [MagniezNayakRolandSantha2011].

## Main statements

* `freshValidationChecker_answer`: the complete fresh-checker specification.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms
open scoped Classical

/-- Establish the fresh validation checker contract by combining witness soundness, a
finite-seed failure bound for search and fresh extraction, and the total checker cost bound. -/
theorem freshValidationChecker_answer : FreshValidationChecker := by
  intro n adj U kcs ncs r' c₀ hκk hκn
  refine ⟨fun stape ntape => triCheckFresh_sound adj U kcs ncs r' c₀ stape ntape, ?_,
    fun stape ntape => fresh_cost_le adj U kcs ncs r' c₀ hκn stape ntape⟩
  intro hex
  letI := ncs.seedFin
  letI := kcs.seedFin
  have hexMarked : ∃ v : Fin n, freshMarked adj U v = true := by
    obtain ⟨v, u₁, hu₁, u₂, hu₂, hne, h1, h2, h3⟩ := hex
    refine ⟨v, ?_⟩
    simp only [freshMarked, decide_eq_true_eq]
    exact ⟨u₁, hu₁, u₂, hu₂, hne, h1, h2, h3⟩
  have hE1 := fresh_E1_card adj U kcs ncs r' c₀ hexMarked
  have hE2 := fresh_E2_card adj U kcs ncs r' c₀
  have hsub :
      (Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        (triCheckFresh adj U kcs ncs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2) ρ.1).1 = none) ⊆
      (Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = none) ∪
      (Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
        (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
          (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none) := by
    intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hρ ⊢
    rw [triCheckFresh_eq] at hρ
    cases hrun : ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
        (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
      (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 with
    | none =>
      exact Or.inl rfl
    | some v =>
      rw [hrun] at hρ
      dsimp only at hρ
      cases hext : (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 with
      | some t =>
        rw [hext] at hρ
        simp at hρ
      | none =>
        exact Or.inr ⟨v, rfl, hext⟩
  have hkey :
      ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        (triCheckFresh adj U kcs ncs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2) ρ.1).1 = none).card : ℕ) *
        (U.card + 1) ^ (min ncs.cExp (c₀ * kcs.cExp)) ≤
      2 * (Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed)) := by
    have hcardR : ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        (triCheckFresh adj U kcs ncs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2) ρ.1).1 = none).card : ℕ) ≤
        ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = none).card : ℕ) +
        ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
        (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
          (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card : ℕ) :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hbase : 0 < U.card + 1 := by omega
    calc ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          (triCheckFresh adj U kcs ncs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2) ρ.1).1 = none).card : ℕ) *
        (U.card + 1) ^ (min ncs.cExp (c₀ * kcs.cExp))
        ≤ (((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = none).card : ℕ) +
          ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card : ℕ)) *
          (U.card + 1) ^ (min ncs.cExp (c₀ * kcs.cExp)) :=
          Nat.mul_le_mul_right _ hcardR
      _ = ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = none).card : ℕ) *
          (U.card + 1) ^ (min ncs.cExp (c₀ * kcs.cExp)) +
        ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card : ℕ) *
          (U.card + 1) ^ (min ncs.cExp (c₀ * kcs.cExp)) := by ring
      _ ≤ ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = none).card : ℕ) *
          (n + 1) ^ ncs.cExp +
        ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card : ℕ) *
          (U.card + 1) ^ (c₀ * kcs.cExp) := by
          refine Nat.add_le_add ?_ ?_
          · have hm : U.card ≤ n := by
              simpa using Finset.card_le_univ U
            exact Nat.mul_le_mul_left _
              ((Nat.pow_le_pow_right hbase (Nat.min_le_left _ _)).trans
                (Nat.pow_le_pow_left (by omega : U.card + 1 ≤ n + 1) _))
          · exact Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hbase (Nat.min_le_right _ _))
      _ ≤ Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) +
          Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) :=
          Nat.add_le_add hE1 hE2
      _ = 2 * (Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed)) := by
          ring
  exact hkey

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
