/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.AnalysisLayer.LocalStochasticUnionBoundStat
public import Mathlib.Data.Finset.Powerset

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.MagicDistill24.AnalysisLayer
open scoped Classical BigOperators

/-- Establishes the local stochastic union bound specified by `LocalStochasticUnionBound`. -/
theorem localStochasticUnionBound : LocalStochasticUnionBound := by
  intro ζ t pp pPh _hp0 _hp1 _ht hnoise
  let A := (Finset.univ : Finset (Fin ζ)).powersetCard (t+1)
  have hpoint (F : Finset (Fin ζ)) : (if t < F.card then pp F else 0) ≤
      ∑ S ∈ A, if S ⊆ F then pp F else 0 := by
    have hnonneg (S : Finset (Fin ζ)) : 0 ≤ (if S ⊆ F then pp F else 0) := by
      split_ifs
      · exact hnoise.1 F
      · exact le_rfl
    by_cases hF : t < F.card
    · obtain ⟨S,hS⟩ := Finset.powersetCard_nonempty.2 (Nat.succ_le_of_lt hF)
      have hSF := (Finset.mem_powersetCard.1 hS).1
      have hScard := (Finset.mem_powersetCard.1 hS).2
      have hSA : S ∈ A := Finset.mem_powersetCard.2 ⟨Finset.subset_univ S,hScard⟩
      rw [ite_eq_left hF]
      have hsingle := Finset.single_le_sum (fun S _ => hnonneg S) hSA
      simpa only [ite_eq_left hSF] using hsingle
    · rw [ite_eq_right hF]
      exact Finset.sum_nonneg (fun S _ => hnonneg S)
  unfold probManyFaults
  rw [Finset.sum_filter]
  calc
    _ ≤ ∑ F : Finset (Fin ζ), ∑ S ∈ A, if S ⊆ F then pp F else 0 :=
      Finset.sum_le_sum fun F _ => hpoint F
    _ = ∑ S ∈ A, ∑ F ∈ Finset.univ.filter (fun F => S ⊆ F), pp F := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ S ∈ A, pPh^(t+1) := by
      apply Finset.sum_le_sum
      intro S hS
      have h := hnoise.2.2 S (Finset.subset_univ S)
      rw [(Finset.mem_powersetCard.1 hS).2] at h
      exact h
    _ = _ := by simp [A,Finset.card_powersetCard]

end Qatlib.Papers.MagicDistill24.AnalysisLayer
