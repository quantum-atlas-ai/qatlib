/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordCuts
import Qatlib.Papers.CommutLCHS26.MainResults.BCHEulerian
import Mathlib.Data.List.Sort

/-!
# Cut counts and Eulerian logarithm coefficients

`reducedWord` removes the constant term from an ordered product of letter exponential series.
For words without repeated letters drawn from an increasing source list, `cutPolynomial` records
the coefficients of powers of this reduced series by counting cuts into increasing blocks.

The closed form in terms of `descents` and `ascents` yields the signed descent formula
`word_log_eulerian` for logarithm coefficients, supporting the BCH expansions used in
[AftabAnTrivisa2026].

## Main statements

* `wordCoefficient_reduced_pow`: identifies reduced series power coefficients with cut
  polynomial coefficients.
* `cutPolynomial_closed`: expresses a cut polynomial using its ascent and descent counts.
* `word_log_eulerian`: computes the logarithm coefficient from word length and descent count.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHCutCounts
open scoped BigOperators MonoidAlgebra
open BCHDynkin BCHWordLie BCHWordCuts
variable {α : Type}

/-- The ordered product of formal letter exponentials with its constant series subtracted. -/
def reducedWord (xs : List α) : PowerSeries (WordAlg α) := wordSeries (xs.map letter) - 1

/-- The reduced word series is graded by word length. -/
theorem reducedWord_graded (xs : List α) : IsGraded (reducedWord xs) := by
  apply IsGraded.sub _ graded_one
  simpa only [letterWord, List.map_map, Function.comp_def, one_smul] using
    letterWord_graded (xs.map (fun a => ((1 : ℚ), a)))

/-- The reduced word series has zero constant coefficient. -/
theorem reducedWord_constant (xs : List α) : (reducedWord xs).constantCoeff = 0 := by
  simp only [reducedWord, map_sub, wordSeries_constant, map_one, sub_self]

variable [LinearOrder α]

/-- A list whose entries lie in a strictly increasing list is a sublist exactly when it is
strictly increasing. -/
theorem sublist_iff_pairwise (xs w : List α) (hxs : xs.Pairwise (· < ·)) (hsub : w ⊆ xs) :
    w.Sublist xs ↔ w.Pairwise (· < ·) := by
  constructor
  · intro h
    exact hxs.sublist h
  · intro h
    exact List.sublist_of_subperm_of_pairwise (List.subperm_of_subset h.nodup hsub) h hxs

/-- For a nonempty word without repeated letters drawn from a strictly increasing list, the
reduced word coefficient is one if the word is increasing and zero otherwise. -/
theorem wordCoefficient_reduced (xs w : List α) (hxs : xs.Pairwise (· < ·))
    (hw : w.Nodup) (hsub : w ⊆ xs) (hne : w ≠ []) :
    wordCoefficient (reducedWord xs) w = if w.Pairwise (· < ·) then 1 else 0 := by
  rw [reducedWord, wordCoefficient_sub, wordCoefficient_word_sublist xs w hxs.nodup hw,
    wordCoefficient_one, if_neg hne, sub_zero]
  simp only [sublist_iff_pairwise xs w hxs hsub]

/-- A prefix containing the first two letters is strictly increasing exactly when the first
letter is smaller than the second and the remaining prefix is strictly increasing. -/
theorem prefix_increasing_iff (a b : α) (w : List α) (i : ℕ) :
    ((a :: b :: w).take (i + 2)).Pairwise (· < ·) ↔
      a < b ∧ ((b :: w).take (i + 1)).Pairwise (· < ·) := by
  simp only [List.take_succ_cons, List.pairwise_cons_cons_iff_of_trans]

/-- For distinct letters drawn from an increasing list, the coefficient in a positive power of
the reduced series splits into a cut after the first letter and an uncut contribution when
the first two letters increase. -/
theorem wordCoefficient_pow_gap (xs : List α) (hxs : xs.Pairwise (· < ·))
    (a b : α) (w : List α) (hw : (a :: b :: w).Nodup) (hsub : (a :: b :: w) ⊆ xs) (k : ℕ) :
    wordCoefficient (reducedWord xs ^ (k + 1)) (a :: b :: w) =
      wordCoefficient (reducedWord xs ^ k) (b :: w) +
        if a < b then wordCoefficient (reducedWord xs ^ (k + 1)) (b :: w) else 0 := by
  rw [wordCoefficient_pow_succ _ (reducedWord_graded xs) (reducedWord_constant xs)]
  simp only [List.length_cons]
  rw [Finset.sum_range_succ']
  have ha : wordCoefficient (reducedWord xs) [a] = 1 := by
    have hsa : [a] ⊆ xs := by
      intro c hc
      have hc' : c = a := by simpa only [List.mem_singleton] using hc
      subst c
      exact hsub (by simp)
    rw [wordCoefficient_reduced xs [a] hxs (by simp) hsa (by simp)]
    simp only [List.pairwise_singleton, ↓reduceIte]
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, ha, one_mul]
  rw [add_comm]
  congr 1
  rw [wordCoefficient_pow_succ _ (reducedWord_graded xs) (reducedWord_constant xs)]
  have hsub' : (b :: w) ⊆ xs := fun _ hc => hsub (List.mem_cons_of_mem a hc)
  by_cases hab : a < b
  · rw [if_pos hab]
    apply Finset.sum_congr rfl
    intro i hi
    have hn : ((a :: b :: w).take (i + 2)) ≠ [] := by simp
    have hn' : ((b :: w).take (i + 1)) ≠ [] := by simp
    have hl := wordCoefficient_reduced xs _ hxs hw.take
      (fun _ hc => hsub (List.mem_of_mem_take hc)) hn
    simp only [List.take_succ_cons] at hl
    rw [hl, wordCoefficient_reduced xs ((b :: w).take (i + 1)) hxs hw.tail.take
      (fun _ hc => hsub' (List.mem_of_mem_take hc)) hn']
    simp only [List.take_succ_cons, List.pairwise_cons_cons_iff_of_trans, hab, true_and,
      List.drop_succ_cons]
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i hi
    have hn : ((a :: b :: w).take (i + 2)) ≠ [] := by simp
    have hl := wordCoefficient_reduced xs _ hxs hw.take
      (fun _ hc => hsub (List.mem_of_mem_take hc)) hn
    simp only [List.take_succ_cons] at hl
    rw [hl]
    simp only [List.pairwise_cons_cons_iff_of_trans, hab, false_and, ↓reduceIte, zero_mul]

/-- The polynomial counting cuts into increasing blocks, defined recursively by a factor `X + 1`
at an ascent and `X` otherwise. -/
def cutPolynomial : List α → Polynomial ℚ
  | [] => 1
  | [_] => Polynomial.X
  | a :: b :: w => (Polynomial.X + if a < b then 1 else 0) * cutPolynomial (b :: w)

/-- The cut polynomial of a nonempty word has zero constant coefficient. -/
theorem cutPolynomial_zero (a : α) (w : List α) : (cutPolynomial (a :: w)).coeff 0 = 0 := by
  induction w generalizing a with
  | nil => simp only [cutPolynomial, Polynomial.coeff_X_zero]
  | cons b w ih => rw [cutPolynomial, Polynomial.mul_coeff_zero, ih, mul_zero]

omit [LinearOrder α] in

/-- The empty word coefficient of a power of the reduced series is one precisely for the zeroth
power. -/
theorem wordCoefficient_pow_empty (xs : List α) (k : ℕ) :
    wordCoefficient (reducedWord xs ^ k) [] = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp only [pow_zero, wordCoefficient_one, ↓reduceIte]
  | succ k =>
    simp only [wordCoefficient, List.length_nil, PowerSeries.coeff_zero_eq_constantCoeff,
      map_pow, reducedWord_constant, zero_pow (by omega : k + 1 ≠ 0),
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    rfl

/-- For a word without repeated letters drawn from an increasing list, its coefficient in the
kth power of the reduced series equals the kth coefficient of its cut polynomial. -/
theorem wordCoefficient_reduced_pow (xs : List α) (hxs : xs.Pairwise (· < ·))
    (w : List α) (hw : w.Nodup) (hsub : w ⊆ xs) (k : ℕ) :
    wordCoefficient (reducedWord xs ^ k) w = (cutPolynomial w).coeff k := by
  induction w generalizing k with
  | nil => simp only [wordCoefficient_pow_empty, cutPolynomial, Polynomial.coeff_one]
  | cons a w ih =>
    cases k with
    | zero => rw [pow_zero, wordCoefficient_one, if_neg (by simp), cutPolynomial_zero]
    | succ k =>
      cases w with
      | nil =>
        rw [wordCoefficient_pow_succ _ (reducedWord_graded xs) (reducedWord_constant xs)]
        have ha : wordCoefficient (reducedWord xs) [a] = 1 := by
          rw [wordCoefficient_reduced xs [a] hxs hw hsub (by simp)]
          simp only [List.pairwise_singleton, ↓reduceIte]
        simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton,
          List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
          ha, one_mul, wordCoefficient_pow_empty, cutPolynomial, Polynomial.coeff_X]
        by_cases hk : k = 0
        · subst k; rfl
        · have hk' : 1 ≠ k + 1 := by omega
          simp only [hk, hk', ↓reduceIte]
      | cons b w =>
        have hsub' : (b :: w) ⊆ xs := fun _ hc => hsub (List.mem_cons_of_mem a hc)
        rw [wordCoefficient_pow_gap xs hxs a b w hw hsub k,
          ih hw.tail hsub' k, ih hw.tail hsub' (k + 1)]
        rw [cutPolynomial, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul]
        by_cases hab : a < b <;>
          simp only [hab, ↓reduceIte, one_mul, zero_mul, Polynomial.coeff_zero, add_zero]

/-- The degree of a cut polynomial is at most the word length. -/
theorem cutPolynomial_degree (w : List α) : (cutPolynomial w).natDegree ≤ w.length := by
  cases w with
  | nil => simp only [cutPolynomial, Polynomial.natDegree_one, List.length_nil, le_refl]
  | cons a w =>
    induction w generalizing a with
    | nil => simp only [cutPolynomial, Polynomial.natDegree_X, List.length_singleton, le_refl]
    | cons b w ih =>
      rw [cutPolynomial]
      have hf : (Polynomial.X + if a < b then 1 else 0 : Polynomial ℚ).natDegree ≤ 1 := by
        by_cases hab : a < b
        · simpa only [hab, ↓reduceIte, Polynomial.natDegree_X, Polynomial.natDegree_one,
            max_eq_left (by omega : 0 ≤ 1)] using
            (Polynomial.natDegree_add_le (Polynomial.X : Polynomial ℚ) 1)
        · simp only [hab, ↓reduceIte, add_zero, Polynomial.natDegree_X, le_refl]
      exact Polynomial.natDegree_mul_le.trans
          (by have h := ih b; simp only [List.length_cons] at *; omega)

/-- The number of adjacent strict decreases in a word. -/
def descents : List α → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: w => (if b < a then 1 else 0) + descents (b :: w)

/-- The number of adjacent strict increases in a word. -/
def ascents : List α → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: w => (if a < b then 1 else 0) + ascents (b :: w)

/-- For a nonempty word without repeated letters, the numbers of descents and ascents sum to one
less than its length. -/
theorem gap_count (a : α) (w : List α) (hw : (a :: w).Nodup) :
    descents (a :: w) + ascents (a :: w) + 1 = (a :: w).length := by
  induction w generalizing a with
  | nil => simp only [descents, ascents, zero_add, List.length_singleton]
  | cons b w ih =>
    have hne : a ≠ b := by
      intro he
      exact (List.nodup_cons.mp hw).1 (by simp [he])
    have ht := ih b hw.tail
    by_cases hab : a < b
    · have hba : ¬ b < a := not_lt_of_ge (le_of_lt hab)
      simp only [descents, ascents, hab, hba, ↓reduceIte, zero_add, List.length_cons] at *
      omega
    · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hne)
      simp only [descents, ascents, hab, hba, ↓reduceIte, zero_add, List.length_cons] at *
      omega

/-- For a nonempty word without repeated letters, the cut polynomial is `X` to the number of
descents plus one times `1 + X` to the number of ascents. -/
theorem cutPolynomial_closed (a : α) (w : List α) (hw : (a :: w).Nodup) :
    cutPolynomial (a :: w) = Polynomial.X ^ (descents (a :: w) + 1) *
      (1 + Polynomial.X) ^ ascents (a :: w) := by
  induction w generalizing a with
  | nil => simp only [cutPolynomial, descents, ascents, zero_add, pow_one, pow_zero, mul_one]
  | cons b w ih =>
    rw [cutPolynomial, ih b hw.tail]
    have hne : a ≠ b := by
      intro he
      exact (List.nodup_cons.mp hw).1 (by simp [he])
    by_cases hab : a < b
    · have hba : ¬ b < a := not_lt_of_ge (le_of_lt hab)
      simp only [descents, ascents, hab, hba, ↓reduceIte, zero_add, pow_add, pow_one]
      ring
    · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hne)
      simp only [descents, ascents, hab, hba, ↓reduceIte, zero_add, add_zero, pow_add, pow_one]
      ring

/-- The coefficient of a nonempty word without repeated letters in the logarithm of an
increasing exponential product is its signed descent weight, with denominator the length
times the corresponding binomial coefficient. This supplies the word coefficients used in
[AftabAnTrivisa2026]. -/
theorem word_log_eulerian (xs : List α) (hxs : xs.Pairwise (· < ·))
    (a : α) (w : List α) (hw : (a :: w).Nodup) (hsub : (a :: w) ⊆ xs) :
    (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) (a :: w).length).coeff
        (FreeMonoid.ofList (a :: w)) =
      (-1 : ℚ) ^ descents (a :: w) /
        (((a :: w).length : ℚ) * (((a :: w).length - 1).choose (descents (a :: w)) : ℚ)) := by
  have he : wordCoefficient (BCHWordLog.logSeries (wordSeries (xs.map letter))) (a :: w) =
      (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) (a :: w).length).coeff
        (FreeMonoid.ofList (a :: w)) := by
    simp only [wordCoefficient, BCHWordLog.logSeries, PowerSeries.coeff_mk]
  rw [← he, wordCoefficient_log]
  change (∑ k ∈ Finset.range (a :: w).length, ((-1 : ℚ) ^ k / (k + 1)) *
    wordCoefficient (reducedWord xs ^ (k + 1)) (a :: w)) = _
  simp_rw [wordCoefficient_reduced_pow xs hxs (a :: w) hw hsub]
  rw [← BCHEulerian.logarithmWeight_eq_sum _ _ (cutPolynomial_degree (a :: w)),
    cutPolynomial_closed a w hw, BCHEulerian.logarithmWeight_cutPolynomial]
  have h := gap_count a w hw
  have h' : descents (a :: w) + ascents (a :: w) = (a :: w).length - 1 := by omega
  have hq : (descents (a :: w) : ℚ) + ascents (a :: w) + 1 = ((a :: w).length : ℚ) := by
    exact_mod_cast h
  rw [hq, h']

end Qatlib.Papers.CommutLCHS26.MainResults.BCHCutCounts
