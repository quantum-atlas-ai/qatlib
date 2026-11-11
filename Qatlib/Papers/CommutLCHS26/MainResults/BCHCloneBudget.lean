/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordPowers

/-!
# Clone multiplicities in BCH coefficient bounds

This module counts distinct labeled copies of repeated letters and the factorial multiplicities
arising when their labels are forgotten. These identities provide the combinatorial
normalization for BCH commutator bounds in [AftabAnTrivisa2026].

The functional `wordFunctional` extends a real function on words rationally linearly. The
theorem `sum_normalized_clone_sum` converts normalized clone permutation sums into a sum over
all words of a fixed length.

## Main statements

* `clone_permutation_word_sum`: Forgetting copy labels in the sum of clone permutations yields
  `factorialMass m` times the part of the base-letter power with the prescribed multiplicities.
* `normalized_clone_sum`: Dividing the sum of a word function over clone permutations by
  `factorialMass m` gives its word functional on the selected multiplicity component.
* `sum_normalized_clone_sum`: Summing factorial-normalized clone permutation sums over all
  multidegrees of total degree `n` equals summing the word function over all length-`n` indexed
  words.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHCloneBudget

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHMultilinear BCHPolarCoeff BCHPolarization BCHMultidegree
open BCHExpansion BCHWordPowers

variable {Γ : ℕ}

/-- The labeled copies in a single clone block are pairwise distinct. -/
theorem cloneBlock_nodup (m : Fin Γ → ℕ) (i : Fin Γ) : (cloneBlock m i).Nodup := by
  apply List.nodup_ofFn.mpr
  intro j k h
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using! h

/-- Every labeled copy in the clone block for `i` has base label `i`. -/
theorem cloneBlock_base (m : Fin Γ → ℕ) (i : Fin Γ) (j : Σ i, Fin (m i))
    (hj : j ∈ cloneBlock m i) : j.1 = i := by
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
  rfl

/-- The complete clone word contains no repeated labeled copies. -/
theorem cloneWord_nodup (m : Fin Γ → ℕ) : (cloneWord m).Nodup :=
  clone_list_nodup (List.finRange Γ) (List.nodup_finRange Γ) (cloneBlock m)
    (cloneBlock_nodup m) Sigma.fst (cloneBlock_base m)

/-- The finite set of labeled copies belonging to the clone block for `i`. -/
def cloneSet (m : Fin Γ → ℕ) (i : Fin Γ) : Finset (Σ i, Fin (m i)) := by
  classical
  exact (cloneBlock m i).toFinset

/-- The clone set for label `i` has exactly `m i` elements. -/
theorem cloneSet_card (m : Fin Γ → ℕ) (i : Fin Γ) : (cloneSet m i).card = m i := by
  classical
  rw [cloneSet, List.toFinset_card_of_nodup (cloneBlock_nodup m i)]
  exact List.length_ofFn

/-- Clone sets belonging to distinct base labels are disjoint. -/
theorem cloneSet_disjoint (m : Fin Γ → ℕ) :
    Pairwise (fun i j => Disjoint (cloneSet m i) (cloneSet m j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro t hti htj
  have hi : t ∈ cloneBlock m i := by simpa only [cloneSet, List.mem_toFinset] using! hti
  have hj : t ∈ cloneBlock m j := by simpa only [cloneSet, List.mem_toFinset] using! htj
  exact hij ((cloneBlock_base m i t hi).symm.trans (cloneBlock_base m j t hj))

/-- The letter-count multidegree of the clone word equals the block degree of its clone sets. -/
theorem cloneWord_degree (m : Fin Γ → ℕ) :
    wordCounts (cloneWord m) = blockDegree Finset.univ (cloneSet m) := by
  rw [wordCounts_eq_squarefree _ (cloneWord_nodup m)]
  unfold blockDegree
  congr 1
  ext t
  simp only [cloneWord, cloneSet, List.mem_toFinset, List.mem_flatMap,
    List.mem_finRange, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- Rewrites the sum of polynomial variables over a clone set as the sum over its explicit copy
indices. -/
theorem cloneSet_sum (m : Fin Γ → ℕ) (i : Fin Γ) :
    (∑ j ∈ cloneSet m i, (MvPolynomial.X j : MvPolynomial (Σ i, Fin (m i)) ℚ)) =
      ∑ k : Fin (m i), MvPolynomial.X (⟨i, k⟩ : Σ i, Fin (m i)) := by
  classical
  rw [cloneSet, List.sum_toFinset _ (cloneBlock_nodup m i)]
  simp only [cloneBlock, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- The rational product of the factorials of the multiplicities `m i`. -/
def factorialMass (m : Fin Γ → ℕ) : ℚ := ∏ i, (m i).factorial

/-- The product of multiplicity factorials is nonzero. -/
theorem factorialMass_ne_zero (m : Fin Γ → ℕ) : factorialMass m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (m i)

/-- The rational linear functional extending a real-valued function on lists to the rational
word algebra. -/
def wordFunctional {α : Type} (F : List α → ℝ) : WordAlg α →ₗ[ℚ] ℝ :=
  Finsupp.linearCombination ℚ (fun w : FreeMonoid α => F w.toList) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- Applying `wordFunctional F` to the basis word `w` returns `F w`. -/
theorem wordFunctional_word {α : Type} (F : List α → ℝ) (w : List α) :
    wordFunctional F (word w) = F w := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single (FreeMonoid.ofList w) 1) = F w
  rw [Finsupp.linearCombination_single, one_smul, FreeMonoid.toList_ofList]

/-- Tagging a power of the sum of clone letters equals scaling the corresponding base-letter
power by the clone-variable sums. -/
theorem tag_letter_sum_power (m : Fin Γ → ℕ) (n : ℕ) :
    tagWords Sigma.fst ((∑ j : Σ i, Fin (m i), letter j) ^ n) =
      scaleWords (fun i => ∑ j ∈ cloneSet m i,
        (MvPolynomial.X j : MvPolynomial (Σ i, Fin (m i)) ℚ))
          ((∑ i : Fin Γ, letter i) ^ n) := by
  rw [map_pow, map_pow]
  congr 1
  simp only [tagWords, scaleWords, map_sum, evaluateWords_letter, cloneSet_sum,
    Finset.sum_smul, Fintype.sum_sigma]

/-- Forgetting copy labels in the sum of clone permutations yields `factorialMass m` times the
part of the base-letter power with the prescribed multiplicities. -/
theorem clone_permutation_word_sum (m : Fin Γ → ℕ) :
    (∑ w ∈ permutationWords (cloneWord m), word (w.map Sigma.fst)) =
      factorialMass m • selectWords (expandedWord m)
        ((∑ i : Fin Γ, letter i) ^ (cloneWord m).length) := by
  have hex := extract_tagWords Sigma.fst (cloneWord m)
    ((∑ j : Σ i, Fin (m i), letter j) ^ (cloneWord m).length)
  rw [tag_letter_sum_power, cloneWord_degree, selectWords_letter_sum_pow, map_sum] at hex
  simp only [evaluate_relabel_word] at hex
  have hscale := extract_scaleWords (cloneSet m) (cloneSet_disjoint m) (expandedWord m) (fun i => by
    rw [cloneSet_card]
    simpa only [expandedWord, if_pos (List.mem_finRange i)] using!
      count_expanded_list (List.finRange Γ) (List.nodup_finRange Γ) m i)
    ((∑ i : Fin Γ, letter i) ^ (cloneWord m).length)
  change extractCoefficient (blockDegree Finset.univ (cloneSet m))
    (scaleWords (fun i => ∑ j ∈ cloneSet m i,
      (MvPolynomial.X j : MvPolynomial (Σ i, Fin (m i)) ℚ))
        ((∑ i : Fin Γ, letter i) ^ (cloneWord m).length)) = _ at hscale
  rw [← hex, hscale]
  simp only [cloneSet_card, factorialMass]

/-- Dividing the sum of a word function over clone permutations by `factorialMass m` gives its
word functional on the selected multiplicity component. -/
theorem normalized_clone_sum (m : Fin Γ → ℕ) (F : List (Fin Γ) → ℝ) :
    (factorialMass m : ℝ)⁻¹ *
      (∑ w ∈ permutationWords (cloneWord m), F (w.map Sigma.fst)) =
        wordFunctional F (selectWords (expandedWord m)
          ((∑ i : Fin Γ, letter i) ^ (cloneWord m).length)) := by
  have h := congrArg (wordFunctional F) (clone_permutation_word_sum m)
  simp only [map_sum, wordFunctional_word, map_smul] at h
  rw [← Rat.cast_smul_eq_qsmul ℝ, smul_eq_mul] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast factorialMass_ne_zero m

/-- Summing factorial-normalized clone permutation sums over all multidegrees of total degree
`n` equals summing the word function over all length-`n` indexed words. -/
theorem sum_normalized_clone_sum (n : ℕ) (F : List (Fin Γ) → ℝ) :
    (∑ m ∈ multidegrees Γ n, (factorialMass m : ℝ)⁻¹ *
      ∑ w ∈ permutationWords (cloneWord m), F (w.map Sigma.fst)) =
        ∑ f : Fin n → Fin Γ, F (List.ofFn f) := by
  calc
    _ = ∑ m ∈ multidegrees Γ n, wordFunctional F (selectWords (expandedWord m)
        ((∑ i : Fin Γ, letter i) ^ n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [normalized_clone_sum, cloneWord_length, (mem_multidegrees m).mp hm]
    _ = wordFunctional F ((∑ i : Fin Γ, letter i) ^ n) := by
      rw [← map_sum, ← homogeneous_multidegree_sum _ (letter_sum_pow_support_length n)]
    _ = _ := by
      rw [letter_sum_pow, map_sum]
      exact Finset.sum_congr rfl fun f _ => wordFunctional_word F (List.ofFn f)

end Qatlib.Papers.CommutLCHS26.MainResults.BCHCloneBudget
