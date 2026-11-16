/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StarDecompSim10.ForestColors.WidthSupport
public import Qatlib.Papers.StarDecompSim10.MainResults.StarSupport

@[expose] public section

/-! # Preserved closed source mathematics with the full recurrence proved

Fixed1003.3683v2. Algebra and finite ancestor locality are certified;
no coherent quantum simulator or precision/runtime bridge is asserted.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.StarDecompSim10.MainResults.MaskSum
open Finset
open scoped BigOperators
open Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition
open Qatlib.Papers.StarDecompSim10.ForestColors
open Qatlib.Papers.StarDecompSim10.ForestColors.WidthSupport
variable {N d : ℕ}

/-- Preserved complete colorWeight_eq_sum_pieces mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem sumPieces (O : SparseOrb N d) (w : Fin N → Fin N → ℂ)
    (x y : Fin N) (c : Fin d) :
    colorWeight O c w x y = ∑ t : Fin 6, piece O w c t x y := by
  by_cases he : edgeColor O x y = some c
  · have hb : starColor O c (min x y) < 6 :=
      sixColors (parent O c) (min x y)
    have hsingle : (∑ t : Fin 6, piece O w c t x y) =
        piece O w c ⟨starColor O c (min x y), hb⟩ x y := by
      refine Finset.sum_eq_single _ ?_ ?_
      · intro t _ ht
        unfold piece
        rw [ite_eq_right]
        rintro ⟨-, hct⟩
        exact ht (Fin.ext hct.symm)
      · intro ht0
        exact absurd (Finset.mem_univ _) ht0
    calc colorWeight O c w x y = w x y := by
          rw [colorWeight, ite_eq_left he]
      _ = piece O w c ⟨starColor O c (min x y), hb⟩ x y := by
          unfold piece
          rw [ite_eq_left]
          exact ⟨he, rfl⟩
      _ = ∑ t : Fin 6, piece O w c t x y := hsingle.symm
  · calc colorWeight O c w x y = 0 := by
          rw [colorWeight, ite_eq_right he]
      _ = ∑ t : Fin 6, piece O w c t x y := by
          rw [Finset.sum_eq_zero]
          intro t _
          unfold piece
          rw [ite_eq_right]
          rintro ⟨he', -⟩
          exact he he'

/-- Preserved complete star_decomposition mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem sumGalaxy (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ)
    (hw : ∀ x y, ¬ G.Adj x y → w x y = 0) (x y : Fin N) :
    w x y = ∑ j : Fin d × Fin 6, piece O w j.1 j.2 x y := by
  rw [weight_decomposition O hG w hw x y]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  exact Finset.sum_congr rfl fun c _ => sumPieces O w x y c

/-! ## Query complexity of the summands -/

/-- Preserved complete hamiltonian_star_decomposition mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem fullDecomp (O : SparseOrb N d) {G : SimpleGraph (Fin N)}
    (hG : ListsGraph O G) (w : Fin N → Fin N → ℂ)
    (hw : ∀ x y, ¬ G.Adj x y → w x y = 0) :
    Fintype.card (Fin d × Fin 6) = 6 * d ∧
      (∀ x y, w x y = ∑ j : Fin d × Fin 6, piece O w j.1 j.2 x y) ∧
      (∀ j : Fin d × Fin 6, IsGalaxy (fun x y => piece O w j.1 j.2 x y)) ∧
      (∀ (j : Fin d × Fin 6) (x : Fin N),
        (incQuerySet O j.1 x).card +
            (reach (parent O j.1) (logStar N + 1) x).card
          ≤ 2 * d + (logStar N + 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_prod]
    simp
    omega
  · intro x y
    exact sumGalaxy O hG w hw x y
  · intro j
    exact pieceGalaxy O hG w j.1 j.2
  · intro j x
    exact pieceQueries O j.1 x

end Qatlib.Papers.StarDecompSim10.MainResults.MaskSum
