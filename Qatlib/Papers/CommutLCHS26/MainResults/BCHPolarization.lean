/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarWord
import Qatlib.Papers.CommutLCHS26.MainResults.BCHPhi

/-!
# Position tagging and word polarization

`wordCounts` records letter multiplicities, while `tagWords` attaches one polynomial variable to
each position and relabels its base letter. The linear map `extractCoefficient` extracts a fixed
multidegree from the polynomial coefficients of `PolarAlg`.

Coefficient extraction after tagging is equivalent to selecting a permutation class and
relabeling it. Applied to word logarithms, this identifies the multilinear component with
`BCHPhi.phi`, supporting the polarization development in [AftabAnTrivisa2026].

## Main statements

* `extract_tagWords`: relates multidegree extraction to word selection.
* `extract_tagged_log_phi`: identifies the fully multilinear tagged logarithm coefficient.
* `evaluate_selected_log_list`: evaluates a selected logarithm component as phi.
* `wordCounts_eq_squarefree`: identifies multiplicities with squarefree exponents for distinct
  letters.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarization

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordLie BCHMultilinear BCHPolarCoeff

variable {σ α : Type}

/-- The finitely supported letter multiplicity function of a word. -/
def wordCounts (w : List σ) : σ →₀ ℕ := (w : Multiset σ).toFinsupp

/-- Two words have equal letter multiplicity functions exactly when they are permutations of one
another. -/
theorem wordCounts_eq_iff (w v : List σ) : wordCounts w = wordCounts v ↔ w.Perm v := by
  exact Multiset.toFinsupp.injective.eq_iff.trans Multiset.coe_eq_coe

/-- Prepending a letter adds one to its multiplicity function. -/
theorem wordCounts_cons (j : σ) (w : List σ) :
    wordCounts (j :: w) = Finsupp.single j 1 + wordCounts w := by
  ext i
  by_cases hi : i = j
  · subst i
    simp [wordCounts, add_comm]
  · simp [wordCounts, hi, Ne.symm hi]

/-- The product of the variables indexed by a word is the monomial with its letter
multiplicities as exponents and coefficient one. -/
theorem position_product (w : List σ) :
    (w.map (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).prod =
      MvPolynomial.monomial (wordCounts w) 1 := by
  induction w with
  | nil => simp [wordCounts]
  | cons j w ih =>
    rw [List.map_cons, List.prod_cons, ih, wordCounts_cons]
    change MvPolynomial.monomial (Finsupp.single j 1) 1 * _ = _
    rw [MvPolynomial.monomial_mul, one_mul]

/-- The coefficient at a target word's multiplicities in a variable product is one when the
indexing word is a permutation of the target and zero otherwise. -/
theorem coeff_position_product (xs w : List σ) :
    ((w.map (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).prod).coeff (wordCounts xs) =
        if w.Perm xs then 1 else 0 := by
  rw [position_product, MvPolynomial.coeff_monomial]
  simp only [wordCounts_eq_iff, List.perm_comm]

/-- The word monoid algebra with rational multivariate polynomial coefficients. -/
abbrev PolarAlg (σ α : Type) := MonoidAlgebra (MvPolynomial σ ℚ) (FreeMonoid α)

/-- The word basis element for one letter in the polynomial coefficient word algebra. -/
def polarLetter (i : α) : PolarAlg σ α := MonoidAlgebra.single (FreeMonoid.of i) 1

/-- The algebra homomorphism relabeling each position by its base letter and multiplying it by
its own polynomial variable. -/
def tagWords (base : σ → α) : WordAlg σ →ₐ[ℚ] PolarAlg σ α :=
  evaluateWords (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ) • polarLetter (base j))

/-- The rational linear map extracting a fixed polynomial multidegree from every word
coefficient. -/
def extractCoefficient (d : σ →₀ ℕ) : PolarAlg σ α →ₗ[ℚ] WordAlg α :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (MvPolynomial.lcoeff ℚ d) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- Extracting a polynomial multidegree from a scaled word basis element extracts that
coefficient from its scalar polynomial. -/
theorem extractCoefficient_single (d : σ →₀ ℕ) (w : FreeMonoid α) (c : MvPolynomial σ ℚ) :
    extractCoefficient d (MonoidAlgebra.single w c) =
      MonoidAlgebra.single w (c.coeff d) := by
  change MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun p : MvPolynomial σ ℚ => p.coeff d) (by simp)
      (Finsupp.single w c)) =
    MonoidAlgebra.ofCoeff (Finsupp.single w (c.coeff d))
  rw [Finsupp.mapRange_single]

/-- Tagging a word relabels its letters by `base` and multiplies its coefficient by the product
of its position variables. -/
theorem tagWords_word (base : σ → α) (w : List σ) :
    tagWords base (word w) = MonoidAlgebra.single (FreeMonoid.ofList (w.map base))
      ((w.map (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).prod) := by
  induction w with
  | nil => simp [tagWords, evaluateWords_word, MonoidAlgebra.one_def]
  | cons j w ih =>
    rw [word_cons, map_mul, ih]
    simp [tagWords, evaluateWords_letter, polarLetter, List.map_cons, List.prod_cons,
      FreeMonoid.ofList_cons, MonoidAlgebra.smul_single, MonoidAlgebra.single_mul_single]

/-- Extracting a target word's multiplicities from a tagged word gives its relabeled basis word
if the original word is a permutation of the target, and zero otherwise. -/
theorem extract_tagWords_word (base : σ → α) (xs w : List σ) :
    extractCoefficient (wordCounts xs) (tagWords base (word w)) =
      if w.Perm xs then word (w.map base) else 0 := by
  rw [tagWords_word, extractCoefficient_single, coeff_position_product]
  split_ifs
  · rfl
  · exact MonoidAlgebra.single_zero _

/-- Extracting a target multidegree after tagging is equivalent to selecting its permutation
class and then relabeling the letters. -/
theorem extract_tagWords (base : σ → α) (xs : List σ) (p : WordAlg σ) :
    extractCoefficient (wordCounts xs) (tagWords base p) =
      evaluateWords (fun j => letter (base j)) (selectWords xs p) := by
  have hw (w : List σ) : extractCoefficient (wordCounts xs) (tagWords base (word w)) =
      evaluateWords (fun j => letter (base j)) (selectWords xs (word w)) := by
    rw [extract_tagWords_word, selectWords_word]
    split_ifs
    · rw [evaluateWords_word, word_eq_prod]
      simp only [List.map_map, Function.comp_def]
    · rw [map_zero]
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word, FreeMonoid.ofList_toList] using! hw w.toList
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul c p hp => simp only [map_smul, hp]

/-- The coefficient using each position variable once in the tagged degree `n` logarithm is phi
on the corresponding base letters. -/
theorem extract_tagged_log_phi {n : ℕ} (base : Fin n → α) :
    extractCoefficient (wordCounts (List.finRange n))
      (tagWords base (BCHWordLog.logCoefficient
        (wordSeries ((List.finRange n).map letter)) n)) =
          BCHPhi.phi (fun j => letter (base j)) := by
  exact extract_tagWords base (List.finRange n) _

/-- Evaluating letters as their relabeled basis elements relabels a word. -/
theorem evaluate_relabel_word (f : σ → α) (w : List σ) :
    evaluateWords (fun j => letter (f j)) (word w) = word (w.map f) := by
  rw [evaluateWords_word, word_eq_prod]
  simp only [List.map_map, Function.comp_def]

/-- Word selection commutes with injective relabeling of the target list and the word algebra
element. -/
theorem selectWords_relabel (f : σ → α) (hf : Function.Injective f)
    (xs : List σ) (p : WordAlg σ) :
    selectWords (xs.map f) (evaluateWords (fun j => letter (f j)) p) =
      evaluateWords (fun j => letter (f j)) (selectWords xs p) := by
  have hw (w : List σ) :
      selectWords (xs.map f) (evaluateWords (fun j => letter (f j)) (word w)) =
        evaluateWords (fun j => letter (f j)) (selectWords xs (word w)) := by
    rw [evaluate_relabel_word, selectWords_word, selectWords_word]
    simp only [List.map_perm_map_iff hf]
    split_ifs
    · rw [evaluate_relabel_word]
    · rw [map_zero]
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word, FreeMonoid.ofList_toList] using! hw w.toList
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul c p hp => simp only [map_smul, hp]

/-- Evaluation after relabeling equals evaluation using the composed letter assignment. -/
theorem evaluate_relabel {B : Type} [Ring B] [Algebra ℚ B] (Y : α → B)
    (f : σ → α) (p : WordAlg σ) :
    evaluateWords Y (evaluateWords (fun j => letter (f j)) p) =
      evaluateWords (fun j => Y (f j)) p := by
  have hw (w : List σ) :
      evaluateWords Y (evaluateWords (fun j => letter (f j)) (word w)) =
        evaluateWords (fun j => Y (f j)) (word w) := by
    rw [evaluate_relabel_word, evaluateWords_word, evaluateWords_word]
    simp only [List.map_map, Function.comp_def]
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word, FreeMonoid.ofList_toList] using! hw w.toList
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul c p hp => simp only [map_smul, hp]

/-- For a list without repetitions, evaluating its selected logarithm component gives phi on the
inputs indexed by that list. -/
theorem evaluate_selected_log_list {B : Type} [Ring B] [Algebra ℚ B]
    (Y : σ → B) (xs : List σ) (hx : xs.Nodup) :
    evaluateWords Y (selectWords xs
      (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) xs.length)) =
        BCHPhi.phi (fun i => Y (xs.get i)) := by
  have hxs : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have hlog := BCHWordLog.logCoefficient_map
    (evaluateWords (fun i => letter (xs.get i)))
    (wordSeries ((List.finRange xs.length).map letter)) xs.length
  rw [wordSeries_map] at hlog
  simp only [List.map_map, Function.comp_def, evaluateWords_letter] at hlog
  have hword : (List.finRange xs.length).map (fun i => letter (xs.get i)) =
      xs.map letter := by
    calc
      _ = ((List.finRange xs.length).map xs.get).map letter := by
        rw [List.map_map]; rfl
      _ = xs.map letter := congrArg (List.map letter) hxs
  rw [hword] at hlog
  have hsel := selectWords_relabel xs.get hx.injective_get (List.finRange xs.length)
    (BCHWordLog.logCoefficient (wordSeries ((List.finRange xs.length).map letter)) xs.length)
  rw [hxs] at hsel
  rw [hlog, hsel]
  rw [evaluate_relabel]
  rfl

/-- For a word without repetitions, its letter multiplicity function is the squarefree exponent
function of its underlying finite set. -/
theorem wordCounts_eq_squarefree (xs : List σ) (hx : xs.Nodup) :
    wordCounts xs = squarefree xs.toFinset := by
  ext j
  by_cases hj : j ∈ xs
  · simp [wordCounts, squarefree, hj, (List.nodup_iff_count_eq_one.mp hx) j hj]
  · simp [wordCounts, squarefree, hj]

end Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarization
