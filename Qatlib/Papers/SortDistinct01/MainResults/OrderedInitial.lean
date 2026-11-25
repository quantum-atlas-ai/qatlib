/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SortDistinct01.MainResults.OrderedSearch
public import Qatlib.Papers.SortDistinct01.MainResults.AdversaryMethod

@[expose] public section

/-!
# Initial potential for the ordered input family

Each monotone nonzero Boolean input has one threshold index. Group the
weights of Eq. (9) by the larger threshold. Adding one more threshold
adds exactly a harmonic number, giving the initial potential after the
common normalized initial state removes the inner-product factors.
-/

set_option autoImplicit false

open scoped BigOperators ComplexInnerProductSpace
open Qatlib.Papers.SortDistinct01.MainResults.OrderedSearch

namespace Qatlib.Papers.SortDistinct01.MainResults

/-- An ordered input is the bit string with its first one at the selected index. -/
def sortedInput {N : ℕ} (i : Fin N) : {x : Fin N → Bool // x ≠ fun _ => false} :=
  ⟨fun j => decide (i ≤ j), by
    intro h
    have hi := congrFun h i
    simp at hi⟩

/-- The selected threshold is the first one in the ordered input. -/
theorem firstOne_sortedInput {N : ℕ} (i : Fin N) : firstOne (sortedInput i) = i.val := by
  unfold firstOne
  apply (Nat.find_eq_iff _).2
  constructor
  · refine ⟨i.isLt, ?_⟩
    change decide (i.val ≤ i.val) = true
    exact decide_eq_true le_rfl
  · intro j hj
    rintro ⟨hN, hval⟩
    change decide (i.val ≤ j) = true at hval
    exact (not_le.mpr hj) (of_decide_eq_true hval)

/-- Every monotone nonzero Boolean input is represented by the threshold chosen
at its first one. -/
theorem exists_sortedInput_eq {N : ℕ} (x : {x : Fin N → Bool // x ≠ fun _ => false})
    (hx : Monotone x.val) : ∃ i : Fin N, sortedInput i = x := by
  obtain ⟨hN, hfirst⟩ := Nat.find_spec (exists_index x.property)
  let i : Fin N := ⟨firstOne x, hN⟩
  refine ⟨i, Subtype.ext (funext fun j => ?_)⟩
  change decide (i ≤ j) = x.val j
  by_cases h : i ≤ j
  · rw [decide_eq_true h]
    have hm := hx h
    change x.val i ≤ x.val j at hm
    have ht : x.val i = true := hfirst
    rw [ht] at hm
    cases hj : x.val j
    · exact ((by decide : ¬ (true : Bool) ≤ false) (hj ▸ hm)).elim
    · rfl
  · rw [decide_eq_false h]
    have hj : j.val < firstOne x := lt_of_not_ge h
    have hmin := ((Nat.find_eq_iff (exists_index x.property)).1 rfl).2 j.val hj
    cases ht : x.val j
    · rfl
    · exact (hmin ⟨j.isLt, ht⟩).elim

/-- The source ordered-search weight as a function of the two threshold indices. -/
noncomputable def thresholdWeight (i j : ℕ) : ℝ :=
  if i < j then 1 / ((j : ℝ) - i) else 0

/-- The source weight of two ordered inputs is the reciprocal gap of their thresholds. -/
theorem orderedWeight_sortedInput {N : ℕ} (i j : Fin N) :
    orderedWeight (sortedInput i) (sortedInput j) = thresholdWeight i.val j.val := by
  simp [orderedWeight, thresholdWeight, firstOne_sortedInput]

/-- Adding the last ordered input contributes one harmonic number. -/
private theorem threshold_last_sum (N : ℕ) :
    (∑ i ∈ Finset.range N, thresholdWeight i N) = (harmonic N : ℝ) := by
  rw [← Finset.sum_range_reflect]
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN := Finset.mem_range.1 hi
  have hlt : N - 1 - i < N := by omega
  have hnat : N - 1 - i + (i + 1) = N := by omega
  have hreal : ((N - 1 - i : ℕ) : ℝ) + ((i + 1 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hnat
  have hdiff : (N : ℝ) - ((N - 1 - i : ℕ) : ℝ) = ((i + 1 : ℕ) : ℝ) := by linarith
  rw [thresholdWeight, ite_eq_left hlt, hdiff, one_div]

/-- The triangular sum of harmonic weights equals Eq. (9)'s initial weight sum. -/
theorem threshold_weight_sum (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, thresholdWeight i j) =
      (N : ℝ) * (harmonic N : ℝ) - N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hfirst :
        (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (N + 1), thresholdWeight i j) =
          ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, thresholdWeight i j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_range_succ, thresholdWeight, ite_eq_right (by have := Finset.mem_range.1 hj; omega), add_zero]
    rw [hfirst, Finset.sum_range_succ, thresholdWeight, ite_eq_right (lt_irrefl N), add_zero,
      threshold_last_sum, ih, harmonic_succ]
    push_cast
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Equation (9) on the ordered input family and with a common normalized initial state
gives the initial potential `N * H_N - N`. -/
theorem ordered_initial_potential {Z N : ℕ} (ψ : Fin N → ℕ → QState Z N)
    (ψ₀ : QState Z N) (hinit : ∀ i, ψ i 0 = ψ₀) (hnorm : ‖ψ₀‖ = 1) :
    (∑ i : Fin N, ∑ j : Fin N, orderedWeight (sortedInput i) (sortedInput j) *
      Complex.re ⟪ψ i 0, ψ j 0⟫) = (N : ℝ) * (harmonic N : ℝ) - N := by
  have hinner : Complex.re ⟪ψ₀, ψ₀⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hnorm]
    norm_num
  simp only [hinit, hinner, mul_one, orderedWeight_sortedInput]
  rw [Finset.sum_comm]
  simpa only [← Fin.sum_univ_eq_sum_range] using threshold_weight_sum N

end Qatlib.Papers.SortDistinct01.MainResults
