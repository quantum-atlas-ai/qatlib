/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics
noncomputable section
open scoped BigOperators

variable {I S : Type*} [Fintype I] [Fintype S] [DecidableEq S]

def groupedRecordSum (J : I → S) (z : I → ℝ) (x : S) : ℝ :=
  ∑ i, if J i=x then z i else 0

def groupedRecordSquares (J : I → S) (z : I → ℝ) (x : S) : ℝ :=
  ∑ i, if J i=x then (z i)^2 else 0

omit [Fintype I] in

theorem grouped_product_fiber (J : I → S) (z : I → ℝ) (i j : I) :
    (∑ x : S, (if J i=x then z i else 0)*(if J j=x then z j else 0)) =
      if J i=J j then z i*z j else 0 := by
  rw [Finset.sum_eq_single (J i)]
  · simp [eq_comm]
  · intro x _ hx
    simp [Ne.symm hx]
  · intro h
    exact False.elim (h (Finset.mem_univ (J i)))

theorem grouped_square_expansion (J : I → S) (z : I → ℝ) :
    (∑ x : S, (Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum J z x)^2) =
      ∑ i : I, ∑ j : I, if J i=J j then z i*z j else 0 := by
  calc
    _ = ∑ x : S, ∑ i : I, ∑ j : I,
        (if J i=x then z i else 0)*(if J j=x then z j else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      unfold Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum
      rw [sq, Finset.sum_mul_sum]
    _ = ∑ i : I, ∑ x : S, ∑ j : I,
        (if J i=x then z i else 0)*(if J j=x then z j else 0) := Finset.sum_comm
    _ = ∑ i : I, ∑ j : I, ∑ x : S,
        (if J i=x then z i else 0)*(if J j=x then z j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by simp_rw [Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.grouped_product_fiber]

theorem grouped_squares_mass (J : I → S) (z : I → ℝ) :
    (∑ x : S, Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSquares J z x) = ∑ i : I, (z i)^2 := by
  unfold Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSquares
  rw [Finset.sum_comm]
  simp

variable [DecidableEq I]

theorem collision_streaming_numerator (J : I → S) (z : I → ℝ) :
    (∑ x : S, ((Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum J z x)^2 - Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSquares J z x)) =
      ∑ i : I, ∑ j : I, if i ≠ j ∧ J i=J j then z i*z j else 0 := by
  have hsplit (i j : I) :
      (if i ≠ j ∧ J i=J j then z i*z j else 0) =
      (if J i=J j then z i*z j else 0)-(if i=j then (z i)^2 else 0) := by
    by_cases hij : i=j
    · subst j
      simp [sq]
    · by_cases hsite : J i=J j <;> simp [hij, hsite]
  rw [Finset.sum_sub_distrib,
      Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.grouped_square_expansion, Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.grouped_squares_mass]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  simp

omit [Fintype I] [DecidableEq I] in

 theorem velocity_streaming_statistic {n : ℕ} (J : Fin n → S) (z : Fin n → ℝ) :
    (Fintype.card S : ℝ)/(n*(n-1) : ℕ) *
      (∑ x : S, ((Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum J z x)^2 - Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSquares J z x)) =
    (Fintype.card S : ℝ)/(n*(n-1) : ℕ) *
      (∑ i : Fin n, ∑ j : Fin n, if i ≠ j ∧ J i=J j then z i*z j else 0) := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.collision_streaming_numerator]

end
end Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics

namespace Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics
noncomputable section
open scoped BigOperators
variable {I S : Type*} [Fintype I] [Fintype S] [DecidableEq S]

def groupedRecordCount (J : I → S) (x : S) : ℝ :=
  ∑ i, if J i=x then 1 else 0

omit [Fintype I] in

 theorem shifted_product_fiber (J : I → S) (z : I → ℝ) (τ : S → S) (i j : I) :
    (∑ x : S, (if J i=x then z i else 0)*(if J j=τ x then z j else 0)) =
      if J j=τ (J i) then z i*z j else 0 := by
  rw [Finset.sum_eq_single (J i)]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · intro h
    exact False.elim (h (Finset.mem_univ (J i)))

theorem grouped_shift_expansion (J : I → S) (z : I → ℝ) (τ : S → S) :
    (∑ x : S, Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum J z x*Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum J z (τ x)) =
      ∑ i : I, ∑ j : I, if J j=τ (J i) then z i*z j else 0 := by
  calc
    _ = ∑ x : S, ∑ i : I, ∑ j : I,
        (if J i=x then z i else 0)*(if J j=τ x then z j else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      unfold Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum
      rw [Finset.sum_mul_sum]
    _ = ∑ i : I, ∑ x : S, ∑ j : I,
        (if J i=x then z i else 0)*(if J j=τ x then z j else 0) := Finset.sum_comm
    _ = ∑ i : I, ∑ j : I, ∑ x : S,
        (if J i=x then z i else 0)*(if J j=τ x then z j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by simp_rw [Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.shifted_product_fiber]

theorem grouped_fixed_count (J : I → S) (τ : S → S) :
    (∑ x : S, if τ x=x then Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordCount J x else 0) =
      ∑ i : I, if τ (J i)=J i then (1 : ℝ) else 0 := by
  have hsplit (x : S) :
      (if τ x=x then Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordCount J x else 0) =
      ∑ i : I, if τ x=x then (if J i=x then (1 : ℝ) else 0) else 0 := by
    by_cases hx : τ x=x <;> simp [hx, Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordCount]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (J i)]
  · simp
  · intro x _ hx
    by_cases ht : τ x=x <;> simp [ht, Ne.symm hx]
  · intro h
    exact False.elim (h (Finset.mem_univ (J i)))

variable [DecidableEq I]

theorem spin_streaming_numerator (J : I → S) (z : I → ℝ) (τ : S → S)
    (hz : ∀ i, (z i)^2=1) :
    (∑ x : S, (Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum J z x*Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordSum J z (τ x) -
      if τ x=x then Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.groupedRecordCount J x else 0)) =
    ∑ i : I, ∑ j : I, if i ≠ j ∧ J j=τ (J i) then z i*z j else 0 := by
  have hsplit (i j : I) :
      (if i ≠ j ∧ J j=τ (J i) then z i*z j else 0) =
      (if J j=τ (J i) then z i*z j else 0)-
        (if i=j then (if τ (J i)=J i then (1 : ℝ) else 0) else 0) := by
    by_cases hij : i=j
    · subst j
      simp [← sq, hz, eq_comm]
    · by_cases hsite : J j=τ (J i) <;> simp [hij, hsite]
  rw [Finset.sum_sub_distrib,
      Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.grouped_shift_expansion, Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.grouped_fixed_count]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  simp

theorem ordered_offdiag_swap (f : I → I → ℝ) :
    (∑ i : I, ∑ j : I, if i ≠ j then f j i else 0) =
    ∑ i : I, ∑ j : I, if i ≠ j then f i j else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem ordered_symmetrization (f : I → I → ℝ) :
    (∑ i : I, ∑ j : I, if i ≠ j then (f i j+f j i)/2 else 0) =
    ∑ i : I, ∑ j : I, if i ≠ j then f i j else 0 := by
  have hsplit (i j : I) :
      (if i ≠ j then (f i j+f j i)/2 else 0) =
      ((if i ≠ j then f i j else 0)+(if i ≠ j then f j i else 0))/2 := by
    by_cases hij : i=j <;> simp [hij]
  have hscale (g : I → I → ℝ) :
      (∑ i : I, ∑ j : I, (g i j/2)) = (∑ i : I, ∑ j : I, g i j)/2 := by
    simp only [Finset.sum_div]
  simp_rw [hsplit, add_div, Finset.sum_add_distrib]
  rw [hscale, hscale,
      Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics.ordered_offdiag_swap]
  ring

end
end Qatlib.Concepts.ShadowModels.UStatBackend.GroupedPairStatistics
