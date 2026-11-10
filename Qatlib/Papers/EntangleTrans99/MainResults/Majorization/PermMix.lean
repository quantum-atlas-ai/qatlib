/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EntangleTrans99.MainResults.Majorization.TopK
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.Majorization

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open scoped BigOperators

noncomputable def permMix {D : ℕ} (w : Equiv.Perm (Fin D) → ℝ) (a : Fin D → ℝ) :
    Fin D → ℝ :=
  fun j => ∑ σ, w σ * a (σ j)

theorem majorizes_permMix {D : ℕ} (a : Fin D → ℝ) (w : Equiv.Perm (Fin D) → ℝ)
    (hw0 : ∀ σ, 0 ≤ w σ) (hw1 : ∑ σ, w σ = 1) :
    Majorizes a (permMix w a) := by
  rw [majorizes_iff_forall_subset_sum]
  intro K hK s hcard
  have hterm : ∀ σ : Equiv.Perm (Fin D),
      ∑ i ∈ s, a (σ i) ≤ prefixSum (sortedDesc a) K := by
    intro σ
    rw [← Finset.sum_image (f := a) (g := σ)
      (fun x _ y _ hxy => Equiv.injective _ hxy)]
    exact finset_sum_le_prefixSum a hK (by
      rw [Finset.card_image_of_injective s (Equiv.injective _)]
      exact hcard)
  calc ∑ i ∈ s, permMix w a i
      = ∑ i ∈ s, ∑ σ, w σ * a (σ i) := rfl
    _ = ∑ σ, ∑ i ∈ s, w σ * a (σ i) := Finset.sum_comm
    _ = ∑ σ, w σ * ∑ i ∈ s, a (σ i) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ σ, w σ * prefixSum (sortedDesc a) K :=
        Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hterm σ) (hw0 σ))
    _ = (∑ σ, w σ) * prefixSum (sortedDesc a) K := by rw [Finset.sum_mul]
    _ = prefixSum (sortedDesc a) K := by rw [hw1, one_mul]

theorem majorizes_perm {D : ℕ} (a : Fin D → ℝ) (σ : Equiv.Perm (Fin D)) :
    Majorizes a (fun j => a (σ j)) := by
  rw [majorizes_iff_forall_subset_sum]
  intro K hK s hcard
  rw [← Finset.sum_image (f := a) (g := σ) (fun x _ y _ hxy => Equiv.injective _ hxy)]
  exact finset_sum_le_prefixSum a hK (by
    rw [Finset.card_image_of_injective s (Equiv.injective _)]
    exact hcard)

theorem majorizes_perm_iff {D : ℕ} (a : Fin D → ℝ) (σ : Equiv.Perm (Fin D)) :
    Majorizes (fun j => a (σ j)) a := by
  have h := majorizes_perm (fun j => a (σ j)) σ⁻¹
  simpa [Function.comp_def] using h

end Qatlib.Papers.EntangleTrans99.MainResults.Majorization
