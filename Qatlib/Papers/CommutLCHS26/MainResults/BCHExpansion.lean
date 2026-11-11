/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHMultidegree
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Multidegree expansion of word logarithms

This module organizes homogeneous word logarithm coefficients by finite multiplicity profiles
`multidegrees`. The lists `expandedWord` and `cloneWord` encode repeated letters and distinct
clones with the same multiplicities.

Each selected component evaluates to a factorial normalized `BCHPhi.phi` expression on cloned
inputs. Summing these components gives `word_log_phi_sum`, the multidegree expansion supporting
the commutator analysis in [AftabAnTrivisa2026].

## Main statements

* `homogeneous_multidegree_sum`: decomposes a homogeneous element by multiplicities.
* `evaluate_log_component`: identifies an evaluated component with a normalized cloned phi
  expression.
* `word_log_phi_sum`: sums the phi expressions to recover the full logarithm coefficient.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHExpansion

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordLie BCHWordLog BCHMultilinear BCHPolarization BCHMultidegree

/-- The word listing each finite alphabet letter in order with its prescribed multiplicity. -/
def expandedWord {Γ : ℕ} (m : Fin Γ → ℕ) : List (Fin Γ) :=
  (List.finRange Γ).flatMap (fun i => List.replicate (m i) i)

/-- The ordered list of distinct clones of one letter, indexed by its prescribed multiplicity. -/
def cloneBlock {Γ : ℕ} (m : Fin Γ → ℕ) (i : Fin Γ) : List (Σ i, Fin (m i)) :=
  List.ofFn (fun j : Fin (m i) => (⟨i, j⟩ : Σ i, Fin (m i)))

/-- The ordered concatenation of all clone blocks for a multiplicity profile. -/
def cloneWord {Γ : ℕ} (m : Fin Γ → ℕ) : List (Σ i, Fin (m i)) :=
  (List.finRange Γ).flatMap (cloneBlock m)

/-- The finite set of multiplicity profiles on `Fin Γ` with total degree `n`. -/
def multidegrees (Γ n : ℕ) : Finset (Fin Γ → ℕ) := Finset.finAntidiagonal Γ n

/-- A multiplicity profile belongs to `multidegrees Γ n` exactly when its entries sum to `n`. -/
theorem mem_multidegrees {Γ n : ℕ} (m : Fin Γ → ℕ) :
    m ∈ multidegrees Γ n ↔ ∑ i, m i = n := Finset.mem_finAntidiagonal

/-- The letter count function of a word over a finite alphabet. -/
def multiplicity {Γ : ℕ} (w : List (Fin Γ)) : Fin Γ → ℕ := fun i => wordCounts w i

/-- The sum of the letter multiplicities equals the word length. -/
theorem sum_multiplicity {Γ : ℕ} (w : List (Fin Γ)) : ∑ i, multiplicity w i = w.length := by
  calc
    _ = (wordCounts w).sum (fun _ n => n) :=
      (Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)).symm
    _ = w.length := by
      simpa only [wordCounts, Multiset.toFinsupp_toMultiset, Multiset.coe_card] using!
        (Finsupp.card_toMultiset (wordCounts w)).symm

/-- The expanded word has exactly the prescribed letter multiplicities. -/
theorem multiplicity_expandedWord {Γ : ℕ} (m : Fin Γ → ℕ) :
    multiplicity (expandedWord m) = m := by
  funext i
  simpa only [multiplicity, wordCounts, Multiset.toFinsupp_apply, Multiset.coe_count,
    expandedWord, if_pos (List.mem_finRange i)] using!
      count_expanded_list (List.finRange Γ) (List.nodup_finRange Γ) m i

/-- A word is a permutation of an expanded word exactly when its multiplicity function equals
the prescribed profile. -/
theorem perm_expandedWord_iff {Γ : ℕ} (w : List (Fin Γ)) (m : Fin Γ → ℕ) :
    w.Perm (expandedWord m) ↔ multiplicity w = m := by
  conv_rhs => rw [← multiplicity_expandedWord m]
  change w.Perm (expandedWord m) ↔
    (fun i => wordCounts w i) = (fun i => wordCounts (expandedWord m) i)
  rw [← wordCounts_eq_iff]
  exact ⟨fun h => congrArg (fun d : Fin Γ →₀ ℕ => (fun i => d i)) h,
    fun h => Finsupp.ext (congrFun h)⟩

/-- The length of the clone word is the sum of the prescribed multiplicities. -/
theorem cloneWord_length {Γ : ℕ} (m : Fin Γ → ℕ) : (cloneWord m).length = ∑ i, m i := by
  simp only [cloneWord, cloneBlock, List.length_flatMap, List.length_ofFn]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

/-- An element supported on words of length `n` decomposes as the sum of its selected
multidegree components of total degree `n`. -/
theorem homogeneous_multidegree_sum {Γ n : ℕ} (p : WordAlg (Fin Γ))
    (hp : ∀ w ∈ p.support, w.toList.length = n) :
    p = ∑ m ∈ multidegrees Γ n, selectWords (expandedWord m) p := by
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro w
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, selectWords_coeff]
  by_cases hc : p.coeff w = 0
  · simp only [hc, ite_self, Finset.sum_const_zero]
  have hw : w ∈ p.support := by simpa using! hc
  have hm : multiplicity w.toList ∈ multidegrees Γ n :=
    (mem_multidegrees _).mpr ((sum_multiplicity w.toList).trans (hp w hw))
  symm
  rw [Finset.sum_eq_single (multiplicity w.toList)]
  · rw [if_pos ((perm_expandedWord_iff _ _).mpr rfl)]
  · intro m _ hne
    rw [if_neg]
    intro he
    exact hne ((perm_expandedWord_iff _ _).mp he).symm
  · intro hnot
    exact (hnot hm).elim

/-- Every word in the support of the nth logarithm coefficient has length `n`. -/
theorem word_log_support_length {Γ n : ℕ} (xs : List (Fin Γ)) (w : FreeMonoid (Fin Γ))
    (hw : w ∈ (logCoefficient (wordSeries (xs.map letter)) n).support) : w.toList.length = n := by
  apply letterWord_log_support_length (xs.map (fun i => ((1 : ℚ), i))) n w
  simpa only [letterWord, List.map_map, Function.comp_def, one_smul] using! hw

/-- The nth logarithm coefficient of the ordered product over a finite alphabet is the sum of
its total degree `n` multidegree components. -/
theorem word_log_multidegree_sum (Γ n : ℕ) :
    logCoefficient (wordSeries ((List.finRange Γ).map letter)) n =
      ∑ m ∈ multidegrees Γ n, selectWords (expandedWord m)
        (logCoefficient (wordSeries ((List.finRange Γ).map letter)) n) :=
  homogeneous_multidegree_sum _ (word_log_support_length _)

/-- Evaluating a selected logarithm component gives the multilinear phi expression on its cloned
letters divided by the product of the multiplicity factorials. -/
theorem evaluate_log_component {B : Type} [Ring B] [Algebra ℚ B] {Γ n : ℕ}
    (X : Fin Γ → B) (m : Fin Γ → ℕ) (hm : m ∈ multidegrees Γ n) :
    evaluateWords X (selectWords (expandedWord m)
      (logCoefficient (wordSeries ((List.finRange Γ).map letter)) n)) =
        (∏ i : Fin Γ, (m i).factorial : ℚ)⁻¹ •
          BCHPhi.phi (fun j => X ((cloneWord m).get j).1) := by
  have hlen : (cloneWord m).length = n :=
    (cloneWord_length m).trans ((mem_multidegrees m).mp hm)
  calc
    _ = evaluateWords X (selectWords (expandedWord m)
      (logCoefficient (wordSeries ((List.finRange Γ).map letter)) (cloneWord m).length)) := by
      rw [hlen]
    _ = _ := evaluate_log_sigma_multidegree X m

/-- The evaluated nth word logarithm coefficient is the sum over total degree `n` multiplicities
of factorial normalized phi expressions on cloned letters. -/
theorem evaluate_word_log_phi_sum {B : Type} [Ring B] [Algebra ℚ B] (Γ n : ℕ)
    (X : Fin Γ → B) :
    evaluateWords X (logCoefficient (wordSeries ((List.finRange Γ).map letter)) n) =
      ∑ m ∈ multidegrees Γ n, (∏ i : Fin Γ, (m i).factorial : ℚ)⁻¹ •
        BCHPhi.phi (fun j => X ((cloneWord m).get j).1) := by
  conv_lhs => rw [word_log_multidegree_sum Γ n]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m hm => evaluate_log_component X m hm

/-- The nth logarithm coefficient of an ordered exponential product is the sum of factorial
normalized phi expressions over its multidegrees. This is the expansion used in
[AftabAnTrivisa2026]. -/
theorem word_log_phi_sum {B : Type} [Ring B] [Algebra ℚ B] (Γ n : ℕ)
    (X : Fin Γ → B) :
    logCoefficient (wordSeries ((List.finRange Γ).map X)) n =
      ∑ m ∈ multidegrees Γ n, (∏ i : Fin Γ, (m i).factorial : ℚ)⁻¹ •
        BCHPhi.phi (fun j => X ((cloneWord m).get j).1) := by
  have h := logCoefficient_map (evaluateWords X)
    (wordSeries ((List.finRange Γ).map letter)) n
  rw [wordSeries_map] at h
  simp only [List.map_map, Function.comp_def, evaluateWords_letter] at h
  rw [h]
  exact evaluate_word_log_phi_sum Γ n X

end Qatlib.Papers.CommutLCHS26.MainResults.BCHExpansion
