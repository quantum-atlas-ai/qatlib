/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarWord
import Qatlib.Papers.CommutLCHS26.MainResults.BCHPhi
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarization

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordLie BCHMultilinear BCHPolarCoeff

variable {σ α : Type}

def wordCounts (w : List σ) : σ →₀ ℕ := (w : Multiset σ).toFinsupp

theorem wordCounts_eq_iff (w v : List σ) : wordCounts w = wordCounts v ↔ w.Perm v := by
  exact Multiset.toFinsupp.injective.eq_iff.trans Multiset.coe_eq_coe

theorem wordCounts_cons (j : σ) (w : List σ) :
    wordCounts (j :: w) = Finsupp.single j 1 + wordCounts w := by
  ext i
  by_cases hi : i = j
  · subst i
    simp [wordCounts, add_comm]
  · simp [wordCounts, hi, Ne.symm hi]

theorem position_product (w : List σ) :
    (w.map (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).prod =
      MvPolynomial.monomial (wordCounts w) 1 := by
  induction w with
  | nil => simp [wordCounts]
  | cons j w ih =>
    rw [List.map_cons, List.prod_cons, ih, wordCounts_cons]
    change MvPolynomial.monomial (Finsupp.single j 1) 1 * _ = _
    rw [MvPolynomial.monomial_mul, one_mul]

theorem coeff_position_product (xs w : List σ) :
    ((w.map (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).prod).coeff (wordCounts xs) =
        if w.Perm xs then 1 else 0 := by
  rw [position_product, MvPolynomial.coeff_monomial]
  simp only [wordCounts_eq_iff, List.perm_comm]

abbrev PolarAlg (σ α : Type) := MonoidAlgebra (MvPolynomial σ ℚ) (FreeMonoid α)

def polarLetter (i : α) : PolarAlg σ α := MonoidAlgebra.single (FreeMonoid.of i) 1

def tagWords (base : σ → α) : WordAlg σ →ₐ[ℚ] PolarAlg σ α :=
  evaluateWords (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ) • polarLetter (base j))

def extractCoefficient (d : σ →₀ ℕ) : PolarAlg σ α →ₗ[ℚ] WordAlg α :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (MvPolynomial.lcoeff ℚ d) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem extractCoefficient_single (d : σ →₀ ℕ) (w : FreeMonoid α) (c : MvPolynomial σ ℚ) :
    extractCoefficient d (MonoidAlgebra.single w c) =
      MonoidAlgebra.single w (c.coeff d) := by
  change MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun p : MvPolynomial σ ℚ => p.coeff d) (by simp)
      (Finsupp.single w c)) =
    MonoidAlgebra.ofCoeff (Finsupp.single w (c.coeff d))
  rw [Finsupp.mapRange_single]

theorem tagWords_word (base : σ → α) (w : List σ) :
    tagWords base (word w) = MonoidAlgebra.single (FreeMonoid.ofList (w.map base))
      ((w.map (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).prod) := by
  induction w with
  | nil => simp [tagWords, evaluateWords_word, MonoidAlgebra.one_def]
  | cons j w ih =>
    rw [word_cons, map_mul, ih]
    simp [tagWords, evaluateWords_letter, polarLetter, List.map_cons, List.prod_cons,
      FreeMonoid.ofList_cons, MonoidAlgebra.smul_single, MonoidAlgebra.single_mul_single]

theorem extract_tagWords_word (base : σ → α) (xs w : List σ) :
    extractCoefficient (wordCounts xs) (tagWords base (word w)) =
      if w.Perm xs then word (w.map base) else 0 := by
  rw [tagWords_word, extractCoefficient_single, coeff_position_product]
  split_ifs
  · rfl
  · exact MonoidAlgebra.single_zero _

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

theorem extract_tagged_log_phi {n : ℕ} (base : Fin n → α) :
    extractCoefficient (wordCounts (List.finRange n))
      (tagWords base (BCHWordLog.logCoefficient
        (wordSeries ((List.finRange n).map letter)) n)) =
          BCHPhi.phi (fun j => letter (base j)) := by
  exact extract_tagWords base (List.finRange n) _

theorem evaluate_relabel_word (f : σ → α) (w : List σ) :
    evaluateWords (fun j => letter (f j)) (word w) = word (w.map f) := by
  rw [evaluateWords_word, word_eq_prod]
  simp only [List.map_map, Function.comp_def]

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

theorem wordCounts_eq_squarefree (xs : List σ) (hx : xs.Nodup) :
    wordCounts xs = squarefree xs.toFinset := by
  ext j
  by_cases hj : j ∈ xs
  · simp [wordCounts, squarefree, hj, (List.nodup_iff_count_eq_one.mp hx) j hj]
  · simp [wordCounts, squarefree, hj]

end Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarization
