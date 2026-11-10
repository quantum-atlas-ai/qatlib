/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.CenteredBinomialFibers

theorem cbd_split_fiber_card {α : Type} [DecidableEq α] {η : ℕ} (A B : Finset α)
    (hAB : Disjoint A B) (hA : A.card = η) (hB : B.card = η) (v : ℕ) :
    (((A ∪ B).powerset.filter
      (fun T => (T ∩ A).card = (T ∩ B).card + v)).card)
      = Nat.choose (2 * η) (η + v) := by
  classical
  have hABint : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hAB
  have hnotBoth : ∀ i : α, i ∈ A → i ∉ B := by
    intro i hiA hib
    have hmem : i ∈ A ∩ B := Finset.mem_inter.mpr ⟨hiA, hib⟩
    rw [hABint] at hmem
    exact absurd hmem (by simp)
  set U := A ∪ B with hU
  set φ : Finset α → Finset α := fun T => (T ∩ A) ∪ (B \ T) with hφ
  have hφsubU : ∀ T : Finset α, φ T ⊆ U := by
    intro T i hi
    rcases Finset.mem_union.mp hi with h' | h'
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp h').2
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp h').1

  have hφinvol : ∀ T : Finset α, T ⊆ U → φ (φ T) = T := by
    intro T hTU
    ext i
    by_cases hiA : i ∈ A
    · have hinB : i ∉ B := hnotBoth i hiA
      have hφ1 : i ∈ φ T ↔ i ∈ T := by
        constructor
        · intro h
          rcases Finset.mem_union.mp h with h' | h'
          · exact (Finset.mem_inter.mp h').1
          · exact absurd (Finset.mem_sdiff.mp h').1 hinB
        · intro hT
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hT, hiA⟩))
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h' | h'
        · exact hφ1.mp (Finset.mem_inter.mp h').1
        · exact absurd (Finset.mem_sdiff.mp h').1 hinB
      · intro hT
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hφ1.mpr hT, hiA⟩))
    · by_cases hiB : i ∈ B
      · have hφ2 : i ∈ φ T ↔ ¬(i ∈ T) := by
          constructor
          · intro h
            rcases Finset.mem_union.mp h with h' | h'
            · exact absurd (Finset.mem_inter.mp h').2 hiA
            · exact (Finset.mem_sdiff.mp h').2
          · intro hT
            exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hiB, hT⟩))
        constructor
        · intro h
          rcases Finset.mem_union.mp h with h' | h'
          · exact absurd (Finset.mem_inter.mp h').2 hiA
          · exact by_contra (fun hnT => (Finset.mem_sdiff.mp h').2
              (hφ2.mpr hnT))
        · intro hT
          have hnφ : ¬(i ∈ φ T) := fun hφi => (hφ2.mp hφi) hT
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hiB, hnφ⟩))
      · have hiU : i ∉ U := by
          intro h
          rcases Finset.mem_union.mp h with hiA' | hiB'
          · exact hiA hiA'
          · exact hiB hiB'
        have hiT : i ∉ T := fun h => hiU (hTU h)
        constructor
        · intro h
          rcases Finset.mem_union.mp h with h' | h'
          · exact absurd (Finset.mem_inter.mp h').2 hiA
          · exact absurd (Finset.mem_sdiff.mp h').1 hiB
        · intro h
          exact absurd h hiT

  have hφcard : ∀ T : Finset α, (φ T).card
      = (T ∩ A).card + (B.card - (T ∩ B).card) := by
    intro T
    show ((T ∩ A) ∪ (B \ T)).card
        = (T ∩ A).card + (B.card - (T ∩ B).card)
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hAB)),
      Finset.card_sdiff]
  have hfw : ∀ T : Finset α, (T ∩ A).card = (T ∩ B).card + v →
      (φ T).card = η + v := by
    intro T hTv
    rw [hφcard T, hTv, hB]
    have hle : (T ∩ B).card ≤ η := by
      rw [← hB]; exact Finset.card_le_card (Finset.inter_subset_right)
    omega

  have hφSA : ∀ S : Finset α, φ S ∩ A = S ∩ A := by
    intro S
    ext i
    constructor
    · intro h
      obtain ⟨hφi, hiA⟩ := Finset.mem_inter.mp h
      rcases Finset.mem_union.mp hφi with h' | h'
      · exact h'
      · exact absurd (Finset.mem_sdiff.mp h').1 (hnotBoth i hiA)
    · intro h
      obtain ⟨hiS, hiA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mpr ⟨hiS, hiA⟩)), hiA⟩
  have hφSB : ∀ S : Finset α, φ S ∩ B = B \ S := by
    intro S
    ext i
    constructor
    · intro h
      obtain ⟨hφi, hiB⟩ := Finset.mem_inter.mp h
      rcases Finset.mem_union.mp hφi with h' | h'
      · exact absurd (Finset.mem_inter.mp h').2 (fun hiA => hnotBoth i hiA hiB)
      · exact Finset.mem_sdiff.mpr ⟨hiB, (Finset.mem_sdiff.mp h').2⟩
    · intro h
      obtain ⟨hiB, hiS⟩ := Finset.mem_sdiff.mp h
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hiB, hiS⟩)), hiB⟩
  have hbw : ∀ S : Finset α, S ⊆ U → S.card = η + v →
      (φ S ∩ A).card = (φ S ∩ B).card + v := by
    intro S hSU hSv
    have hunion : (S ∩ A) ∪ (S ∩ B) = S := by
      ext i
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hiS, _⟩ | ⟨hiS, _⟩)
        · exact hiS
        · exact hiS
      · intro hiS
        rcases Finset.mem_union.mp (hSU hiS) with hiA | hiB
        · exact Or.inl ⟨hiS, hiA⟩
        · exact Or.inr ⟨hiS, hiB⟩
    have h1 : (S ∩ A).card + (S ∩ B).card = S.card := by
      conv_rhs => rw [← hunion]
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB))]
    have h2 : (B \ S).card = B.card - (S ∩ B).card := Finset.card_sdiff
    have hle : (S ∩ B).card ≤ η := by
      rw [← hB]; exact Finset.card_le_card (Finset.inter_subset_right)
    rw [hφSA, hφSB, h2]
    omega

  have e : ↥((U.powerset.filter
        (fun T => (T ∩ A).card = (T ∩ B).card + v)))
      ≃ ↥(U.powersetCard (η + v)) :=
    ⟨fun T => ⟨φ T.1, Finset.mem_powersetCard.mpr
        ⟨hφsubU T.1, hfw T.1 (Finset.mem_filter.mp T.2).2⟩⟩,
     fun S => ⟨φ S.1, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (hφsubU S.1),
         hbw S.1 (Finset.mem_powersetCard.mp S.2).1
           (Finset.mem_powersetCard.mp S.2).2⟩⟩,
     fun T => Subtype.ext
       (hφinvol T.1 (Finset.mem_powerset.mp (Finset.mem_filter.mp T.2).1)),
     fun S => Subtype.ext
       (hφinvol S.1 (Finset.mem_powersetCard.mp S.2).1)⟩
  rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_coe,
    Finset.card_powersetCard, hU, Finset.card_union_of_disjoint hAB, hA, hB]
  congr 1
  omega

def cbdFirstHalf (η : ℕ) : Finset (Fin (2 * η)) :=
  Finset.map (Fin.castLEEmb (show η ≤ 2 * η by omega)) Finset.univ

def cbdSecondHalf (η : ℕ) : Finset (Fin (2 * η)) :=
  Finset.univ \ cbdFirstHalf η

private theorem split_fiber_subtype_card {η : ℕ} (A B : Finset (Fin (2 * η)))
    (hAB : Disjoint A B) (hA : A.card = η) (hB : B.card = η)
    (hAU : A ∪ B = Finset.univ) (v : ℕ) :
    Fintype.card {T : Finset (Fin (2 * η)) // (T ∩ A).card = (T ∩ B).card + v}
      = Nat.choose (2 * η) (η + v) := by
  have hgen := cbd_split_fiber_card A B hAB hA hB v
  have hsplit : ((Finset.univ (α := Fin (2 * η))).powerset.filter
      (fun T => (T ∩ A).card = (T ∩ B).card + v)) = (A ∪ B).powerset.filter
      (fun T => (T ∩ A).card = (T ∩ B).card + v) := by
    rw [hAU]
  have e : {T : Finset (Fin (2 * η)) // (T ∩ A).card = (T ∩ B).card + v}
      ≃ ↥(((Finset.univ (α := Fin (2 * η))).powerset.filter
        (fun T => (T ∩ A).card = (T ∩ B).card + v))) :=
    ⟨fun T => ⟨T.1, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), T.2⟩⟩,
     fun T => ⟨T.1, (Finset.mem_filter.mp T.2).2⟩,
     fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e, Fintype.card_coe, hsplit]
  exact hgen

theorem cbd_split_fiber_fin (η v : ℕ) :
    Fintype.card {T : Finset (Fin (2 * η)) //
        (T ∩ cbdFirstHalf η).card = (T ∩ cbdSecondHalf η).card + v}
      = Nat.choose (2 * η) (η + v) := by
  have hFH : (cbdFirstHalf η).card = η := by
    rw [cbdFirstHalf, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hSH : (cbdSecondHalf η).card = η := by
    rw [cbdSecondHalf, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      hFH, Finset.card_univ, Fintype.card_fin]
    omega
  have hDisj : Disjoint (cbdFirstHalf η) (cbdSecondHalf η) := by
    rw [Finset.disjoint_iff_inter_eq_empty, cbdSecondHalf]
    simp
  have hUnion : cbdFirstHalf η ∪ cbdSecondHalf η = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr (fun i => ?_)
    by_cases hi : i ∈ cbdFirstHalf η
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
  exact split_fiber_subtype_card _ _ hDisj hFH hSH hUnion v

theorem cbd_split_fiber_symm (η v : ℕ) :
    Fintype.card {T : Finset (Fin (2 * η)) //
        (T ∩ cbdSecondHalf η).card = (T ∩ cbdFirstHalf η).card + v}
      = Nat.choose (2 * η) (η + v) := by
  have hFH : (cbdFirstHalf η).card = η := by
    rw [cbdFirstHalf, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hSH : (cbdSecondHalf η).card = η := by
    rw [cbdSecondHalf, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      hFH, Finset.card_univ, Fintype.card_fin]
    omega
  have hDisj : Disjoint (cbdSecondHalf η) (cbdFirstHalf η) := by
    rw [Finset.disjoint_iff_inter_eq_empty, cbdSecondHalf]
    simp
  have hUnion : cbdSecondHalf η ∪ cbdFirstHalf η = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr (fun i => ?_)
    by_cases hi : i ∈ cbdFirstHalf η
    · exact Finset.mem_union_right _ hi
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
  exact split_fiber_subtype_card _ _ hDisj hSH hFH hUnion v

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.CenteredBinomialFibers
