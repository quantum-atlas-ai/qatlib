/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLie

/-!
# Word coefficients and prefix cuts

`cutPair` and `cuts` enumerate all factorizations of a word into a prefix and a suffix. They
give convolution formulas for word algebra coefficients and for the length matched series
coefficient `wordCoefficient`.

For graded series, these formulas describe positive powers and formal logarithms. For ordered
exponential products of distinct letters, the coefficients become sublist indicators, providing
the cut counting input for the BCH analysis in [AftabAnTrivisa2026].

## Main statements

* `wordCoeff_mul`: computes a product coefficient by summing over cuts.
* `wordCoefficient_pow_succ`: computes powers using nonempty prefixes when the constant
  coefficient vanishes.
* `wordCoefficient_log`: gives the finite logarithm coefficient sum.
* `wordCoefficient_word_sublist`: computes coefficients for lists without repetitions.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHWordCuts

open scoped BigOperators MonoidAlgebra
open BCHDynkin BCHWordLie
variable {α : Type}

/-- The prefix and suffix word pair obtained by cutting a list at position `i`. -/
def cutPair (w : List α) (i : ℕ) : FreeMonoid α × FreeMonoid α :=
  (FreeMonoid.ofList (w.take i), FreeMonoid.ofList (w.drop i))

/-- Distinct cut positions between zero and the word length give distinct prefix and suffix
pairs. -/
theorem cutPair_injective (w : List α) :
    Set.InjOn (cutPair w) (↑(Finset.range (w.length + 1)) : Set ℕ) := by
  intro i hi j hj h
  have hi' : i ≤ w.length := by
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hi
  have hj' : j ≤ w.length := by
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hj
  have he := congrArg (fun p : FreeMonoid α × FreeMonoid α => p.1.toList.length) h
  simpa only [cutPair, FreeMonoid.toList_ofList, List.length_take, Nat.min_eq_left hi',
    Nat.min_eq_left hj'] using he

/-- The finite set of all prefix and suffix pairs obtained by cutting a word. -/
def cuts (w : List α) : Finset (FreeMonoid α × FreeMonoid α) := by
  classical
  exact (Finset.range (w.length + 1)).image (cutPair w)

/-- A pair belongs to the cuts of a word exactly when its product is that word. -/
theorem mem_cuts_iff (w : List α) (u v : FreeMonoid α) :
    (u, v) ∈ cuts w ↔ u * v = FreeMonoid.ofList w := by
  classical
  unfold cuts
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, hi, h⟩
    change (u, v).1 * (u, v).2 = FreeMonoid.ofList w
    rw [← h]
    simp only [cutPair, ← FreeMonoid.ofList_append, List.take_append_drop]
  · intro h
    have hw : u.toList ++ v.toList = w := by
      simpa only [FreeMonoid.toList_mul, FreeMonoid.toList_ofList] using
          congrArg FreeMonoid.toList h
    apply Finset.mem_image.mpr
    refine ⟨u.toList.length, ?_, ?_⟩
    · simp only [Finset.mem_range, ← hw, List.length_append]
      omega
    · simp only [cutPair, ← hw, List.take_left, List.drop_left, FreeMonoid.ofList_toList]

/-- A word coefficient in a product of word algebra elements is the sum of prefix and suffix
coefficient products over all cuts. -/
theorem wordCoeff_mul (p q : WordAlg α) (w : List α) :
    (p * q).coeff (FreeMonoid.ofList w) = ∑ i ∈ Finset.range (w.length + 1),
      p.coeff (FreeMonoid.ofList (w.take i)) * q.coeff (FreeMonoid.ofList (w.drop i)) := by
  classical
  change (p * q) (FreeMonoid.ofList w) = _
  rw [MonoidAlgebra.mul_apply_antidiagonal p q (FreeMonoid.ofList w)
    (cuts w) (fun {p} => mem_cuts_iff w p.1 p.2)]
  unfold cuts
  rw [Finset.sum_image (cutPair_injective w)]
  rfl

/-- In a graded word power series, a word coefficient vanishes when its length differs from the
series degree. -/
theorem graded_coeff_eq_zero {f : PowerSeries (WordAlg α)} (hf : IsGraded f)
    (n : ℕ) (w : List α) (hn : w.length ≠ n) :
    (PowerSeries.coeff n f).coeff (FreeMonoid.ofList w) = 0 := by
  by_contra h
  have hw : FreeMonoid.ofList w ∈ (PowerSeries.coeff n f).support := by simpa using! h
  exact hn (by simpa only [FreeMonoid.toList_ofList] using
    support_length_of_grading _ n (hf n) _ hw)

/-- The coefficient of a word in the series degree equal to its length. -/
def wordCoefficient (f : PowerSeries (WordAlg α)) (w : List α) : ℚ :=
  (PowerSeries.coeff w.length f).coeff (FreeMonoid.ofList w)

/-- When the left factor is graded, the word coefficient of a series product is the sum of
prefix and suffix word coefficient products over all cuts. -/
theorem wordCoefficient_mul (f g : PowerSeries (WordAlg α)) (hf : IsGraded f)
    (w : List α) :
    wordCoefficient (f * g) w = ∑ i ∈ Finset.range (w.length + 1),
      wordCoefficient f (w.take i) * wordCoefficient g (w.drop i) := by
  classical
  unfold wordCoefficient
  rw [PowerSeries.coeff_mul, MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply]
  simp_rw [wordCoeff_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ w.length := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have ht : (w.take i).length = i := by simp only [List.length_take, Nat.min_eq_left hi']
  have hd : (w.drop i).length = w.length - i := List.length_drop
  rw [ht, hd]
  apply Finset.sum_eq_single (i, w.length - i)
  · intro p hp hne
    have hp' := Finset.mem_antidiagonal.mp hp
    have hp1 : (w.take i).length ≠ p.1 := by
      intro h
      have he : p = (i, w.length - i) := by ext <;> omega
      exact hne he
    rw [graded_coeff_eq_zero hf _ _ hp1, zero_mul]
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr (Nat.add_sub_of_le hi'))).elim

/-- The unit series has word coefficient one on the empty word and zero on every nonempty word. -/
theorem wordCoefficient_one (w : List α) :
    wordCoefficient (1 : PowerSeries (WordAlg α)) w = if w = [] then 1 else 0 := by
  classical
  cases w with
  | nil => simp [wordCoefficient, PowerSeries.coeff_one, MonoidAlgebra.one_def]
  | cons a w =>
    simp only [wordCoefficient, List.length_cons, PowerSeries.coeff_one, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, MonoidAlgebra.coeff_zero,
      List.cons_ne_nil]
    rfl

/-- Word coefficients preserve subtraction. -/
theorem wordCoefficient_sub (f g : PowerSeries (WordAlg α)) (w : List α) :
    wordCoefficient (f - g) w = wordCoefficient f w - wordCoefficient g w := by
  simp only [wordCoefficient, map_sub, MonoidAlgebra.coeff_sub, Finsupp.sub_apply]

/-- For a graded series with zero constant coefficient, a coefficient in its positive power is
the sum over nonempty prefixes of the first factor coefficient times the remaining power
coefficient. -/
theorem wordCoefficient_pow_succ (f : PowerSeries (WordAlg α)) (hf : IsGraded f)
    (hzero : f.constantCoeff = 0) (k : ℕ) (w : List α) :
    wordCoefficient (f ^ (k + 1)) w = ∑ i ∈ Finset.range w.length,
      wordCoefficient f (w.take (i + 1)) * wordCoefficient (f ^ k) (w.drop (i + 1)) := by
  rw [pow_succ', wordCoefficient_mul _ _ hf, Finset.sum_range_succ']
  have hz : wordCoefficient f [] = 0 := by
    simp only [wordCoefficient, List.length_nil, PowerSeries.coeff_zero_eq_constantCoeff, hzero]
    rfl
  simp only [List.take_zero, hz, zero_mul, add_zero]

/-- The logarithm word coefficient is the finite alternating weighted sum of the word
coefficients of positive powers of `f - 1`. -/
theorem wordCoefficient_log (f : PowerSeries (WordAlg α)) (w : List α) :
    wordCoefficient (BCHWordLog.logSeries f) w = ∑ k ∈ Finset.range w.length,
      ((-1 : ℚ) ^ k / (k + 1)) * wordCoefficient ((f - 1) ^ (k + 1)) w := by
  simp only [wordCoefficient, BCHWordLog.logSeries, PowerSeries.coeff_mk,
    BCHWordLog.logCoefficient_finite, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

/-- A power of a letter basis element is the word consisting of that many copies of the letter. -/
theorem letter_pow (a : α) (n : ℕ) : letter a ^ n = word (List.replicate n a) := by
  rw [word_eq_prod, List.map_replicate, List.prod_replicate]

section Discrete
variable [DecidableEq α]

/-- The formal exponential of one letter has coefficient the reciprocal word length factorial on
words consisting only of that letter and zero otherwise. -/
theorem wordCoefficient_generator (a : α) (w : List α) :
    wordCoefficient (generatorSeries (letter a)) w =
      if w = List.replicate w.length a then (w.length.factorial : ℚ)⁻¹ else 0 := by
  classical
  unfold wordCoefficient
  rw [generatorSeries, PowerSeries.coeff_mk, letter_pow]
  change (w.length.factorial : ℚ)⁻¹ * word (List.replicate w.length a) (FreeMonoid.ofList w) = _
  rw [word, MonoidAlgebra.single_apply]
  by_cases h : w = List.replicate w.length a
  · have he : FreeMonoid.ofList (List.replicate w.length a) = FreeMonoid.ofList w := congrArg _ h.symm
    rw [if_pos he, if_pos h, mul_one]
  · have he : FreeMonoid.ofList (List.replicate w.length a) ≠ FreeMonoid.ofList w := by
      intro heq
      apply h
      simpa only [FreeMonoid.toList_ofList] using (congrArg FreeMonoid.toList heq).symm
    rw [if_neg he, if_neg h, mul_zero]

omit [DecidableEq α] in

/-- Every ordered product of letter exponential series has empty word coefficient one. -/
theorem wordCoefficient_word_empty (xs : List α) :
    wordCoefficient (wordSeries (xs.map letter)) [] = 1 := by
  simp only [wordCoefficient, List.length_nil, PowerSeries.coeff_zero_eq_constantCoeff,
    wordSeries_constant]
  simp [MonoidAlgebra.one_def]

/-- For a target word without repetitions, adding a leading exponential letter contributes the
old coefficient and a suffix coefficient when that letter matches the target's first letter. -/
theorem wordCoefficient_word_cons (a : α) (xs : List α) (b : α) (w : List α)
    (hw : (b :: w).Nodup) :
    wordCoefficient (wordSeries ((a :: xs).map letter)) (b :: w) =
      wordCoefficient (wordSeries (xs.map letter)) (b :: w) +
        if b = a then wordCoefficient (wordSeries (xs.map letter)) w else 0 := by
  classical
  change wordCoefficient (generatorSeries (letter a) * wordSeries (xs.map letter)) (b :: w) = _
  rw [wordCoefficient_mul _ _ (generatorSeries_graded _ (grading_letter a)), Finset.sum_range_succ']
  have hzero : wordCoefficient (generatorSeries (letter a)) [] = 1 := by
    simp [wordCoefficient_generator]
  simp only [List.take_zero, List.drop_zero, hzero, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp [wordCoefficient_generator]
    exact add_comm _ _
  · intro i hi hne
    have hi' : i + 1 ≤ (b :: w).length := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using! hi
    have ht : ((b :: w).take (i + 1)).Nodup := hw.take
    have hlen : 2 ≤ ((b :: w).take (i + 1)).length := by
      rw [List.length_take, Nat.min_eq_left hi']
      omega
    have hn : (b :: w).take (i + 1) ≠ List.replicate (((b :: w).take (i + 1)).length) a := by
      intro he
      have h := List.nodup_replicate.mp (he ▸ ht)
      omega
    rw [wordCoefficient_generator, if_neg hn, zero_mul]
  · simp only [List.length_cons, Finset.mem_range, Nat.zero_lt_succ, not_true_eq_false,
      IsEmpty.forall_iff]

/-- For source and target lists without repetitions, the ordered exponential word coefficient is
one exactly when the target is a sublist of the source, and zero otherwise. -/
theorem wordCoefficient_word_sublist (xs w : List α) (hxs : xs.Nodup) (hw : w.Nodup) :
    wordCoefficient (wordSeries (xs.map letter)) w = if w.Sublist xs then 1 else 0 := by
  classical
  induction xs generalizing w with
  | nil => simp only [List.map_nil, wordSeries, List.prod_nil, wordCoefficient_one, List.sublist_nil]
  | cons a xs ih =>
    rcases List.nodup_cons.mp hxs with ⟨ha, hxs⟩
    cases w with
    | nil => simp only [wordCoefficient_word_empty, List.nil_sublist, ↓reduceIte]
    | cons b w =>
      rw [wordCoefficient_word_cons a xs b w hw, ih (b :: w) hxs hw, ih w hxs hw.tail]
      by_cases hba : b = a
      · subst b
        have hn : ¬ (a :: w).Sublist xs := by
          intro hs
          exact ha (hs.subset (by simp))
        simp only [hn, ↓reduceIte, List.cons_sublist_cons, zero_add]
      · simp only [List.cons_sublist_cons', hba, false_and, or_false, ↓reduceIte, add_zero]

end Discrete

end Qatlib.Papers.CommutLCHS26.MainResults.BCHWordCuts
