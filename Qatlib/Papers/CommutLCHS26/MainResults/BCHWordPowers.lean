/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHExpansion
import Mathlib.Data.Fin.Tuple.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHWordPowers

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHMultilinear BCHExpansion

variable {α β : Type}

theorem letter_sum_pow [Fintype α] (n : ℕ) :
    (∑ i : α, letter i) ^ n = ∑ f : Fin n → α, word (List.ofFn f) := by
  induction n with
  | zero => simp [word, MonoidAlgebra.one_def]
  | succ n ih =>
    rw [pow_succ', ih, Finset.sum_mul]
    simp only [Finset.mul_sum, ← word_cons, ← List.ofFn_cons]
    have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => α))
      (fun p => word (List.ofFn (Fin.cons p.1 p.2)))
      (fun f => word (List.ofFn f)) (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using! he

theorem letter_sum_pow_coeff_ofFn [Fintype α] {n : ℕ} (f : Fin n → α) :
    ((∑ i : α, letter i) ^ n).coeff (FreeMonoid.ofList (List.ofFn f)) = 1 := by
  rw [letter_sum_pow]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, word_coeff,
    FreeMonoid.toList_ofList, List.ofFn_inj]
  simp

theorem letter_sum_pow_coeff [Fintype α] (n : ℕ) (w : List α) (hw : w.length = n) :
    ((∑ i : α, letter i) ^ n).coeff (FreeMonoid.ofList w) = 1 := by
  subst n
  simpa only [List.ofFn_get] using! letter_sum_pow_coeff_ofFn w.get

theorem selectWords_letter_sum_pow [Fintype α] (xs : List α) :
    selectWords xs ((∑ i : α, letter i) ^ xs.length) =
      ∑ w ∈ permutationWords xs, word w := by
  rw [selectWords_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [letter_sum_pow_coeff xs.length w ((mem_permutationWords _ _).mp hw).length_eq,
    one_smul]

theorem sum_permutationWords_map {M : Type} [AddCommMonoid M] (f : α → β)
    (hf : Function.Injective f) (xs : List α) (F : List β → M) :
    (∑ w ∈ permutationWords xs, F (w.map f)) =
      ∑ v ∈ permutationWords (xs.map f), F v := by
  have he : permutationWords (xs.map f) = (permutationWords xs).image (List.map f) := by
    simp only [permutationWords, ← List.map_permutations]
    ext v
    simp
  rw [he, Finset.sum_image]
  exact fun _ _ _ _ h => List.map_injective_iff.mpr hf h

theorem letter_sum_pow_support_length [Fintype α] (n : ℕ) (w : FreeMonoid α)
    (hw : w ∈ ((∑ i : α, letter i) ^ n).support) : w.toList.length = n := by
  have hg : BCHDynkin.grading (∑ i : α, letter i) = ∑ i : α, letter i := by
    simp only [map_sum, grading_letter]
  exact support_length_of_grading _ n (grading_pow_of_degree_one _ hg n) w hw

end Qatlib.Papers.CommutLCHS26.MainResults.BCHWordPowers
