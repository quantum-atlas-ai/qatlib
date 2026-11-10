/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarization
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHMultidegree

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordLie BCHWordLog BCHMultilinear BCHPolarCoeff BCHPolarization

variable {σ α : Type}

def scaleWords (r : α → MvPolynomial σ ℚ) : WordAlg α →ₐ[ℚ] PolarAlg σ α :=
  evaluateWords (fun i => r i • polarLetter i)

theorem scaleWords_word (r : α → MvPolynomial σ ℚ) (w : List α) :
    scaleWords r (word w) = MonoidAlgebra.single (FreeMonoid.ofList w) (w.map r).prod := by
  induction w with
  | nil => simp [scaleWords, evaluateWords_word, MonoidAlgebra.one_def]
  | cons i w ih =>
    rw [word_cons, map_mul, ih]
    simp [scaleWords, evaluateWords_letter, polarLetter, List.map_cons, List.prod_cons,
      FreeMonoid.ofList_cons, MonoidAlgebra.smul_single, MonoidAlgebra.single_mul_single]

theorem central_product_counts [Fintype α] (r : α → MvPolynomial σ ℚ) (w : List α) :
    (w.map r).prod = ∏ i : α, (r i) ^ w.count i := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [List.mem_toFinset] at hi
  rw [List.count_eq_zero_of_not_mem hi, pow_zero]

theorem coeff_grouped_word [Fintype α] (s : α → Finset σ)
    (hs : Pairwise (fun i j => Disjoint (s i) (s j))) (v w : List α)
    (hv : ∀ i, v.count i = (s i).card) :
    ((w.map (fun i => (∑ j ∈ s i, MvPolynomial.X j : MvPolynomial σ ℚ))).prod).coeff
      (squarefree (Finset.univ.biUnion s)) =
        if w.Perm v then ∏ i : α, ((s i).card.factorial : ℚ) else 0 := by
  rw [central_product_counts]
  change (∏ i : α, (∑ j ∈ s i, MvPolynomial.X j : MvPolynomial σ ℚ) ^ w.count i).coeff
    (blockDegree Finset.univ s) = _
  rw [coeff_position_blocks Finset.univ s (fun i => w.count i)
    (fun _ _ _ _ hij => hs hij)]
  by_cases hw : w.Perm v
  · rw [if_pos hw]
    apply Finset.prod_congr rfl
    intro i _
    rw [hw.count_eq i, hv i, if_pos rfl]
  · rw [if_neg hw]
    have hnot : ¬∀ i, w.count i = (s i).card := by
      intro hc
      apply hw
      apply List.perm_iff_count.mpr
      intro i
      rw [hc i, hv i]
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (Ne.symm hi))

theorem extract_scaleWords [Fintype α] (s : α → Finset σ)
    (hs : Pairwise (fun i j => Disjoint (s i) (s j))) (v : List α)
    (hv : ∀ i, v.count i = (s i).card) (p : WordAlg α) :
    extractCoefficient (squarefree (Finset.univ.biUnion s))
      (scaleWords (fun i => (∑ j ∈ s i, MvPolynomial.X j : MvPolynomial σ ℚ)) p) =
        (∏ i : α, ((s i).card.factorial : ℚ)) • selectWords v p := by
  have hw (w : List α) :
      extractCoefficient (squarefree (Finset.univ.biUnion s))
        (scaleWords (fun i => (∑ j ∈ s i, MvPolynomial.X j : MvPolynomial σ ℚ)) (word w)) =
          (∏ i : α, ((s i).card.factorial : ℚ)) • selectWords v (word w) := by
    rw [scaleWords_word, extractCoefficient_single, coeff_grouped_word s hs v w hv,
      selectWords_word]
    split_ifs
    · simp [word, MonoidAlgebra.smul_single]
    · exact (MonoidAlgebra.single_zero _).trans (smul_zero _).symm
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word, FreeMonoid.ofList_toList] using! hw w.toList
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]
  | smul c p hp => simp only [map_smul, hp, smul_comm c]

theorem clone_blocks_disjoint (positions : α → List σ) (base : σ → α)
    (hbase : ∀ i, ∀ j ∈ positions i, base j = i) :
    Pairwise (fun i j => Disjoint (positions i).toFinset (positions j).toFinset) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro t hti htj
  exact hij ((hbase i t (List.mem_toFinset.mp hti)).symm.trans
    (hbase j t (List.mem_toFinset.mp htj)))

theorem clone_list_nodup (xs : List α) (hx : xs.Nodup) (positions : α → List σ)
    (hp : ∀ i, (positions i).Nodup) (base : σ → α)
    (hbase : ∀ i, ∀ j ∈ positions i, base j = i) : (xs.flatMap positions).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => hp i, hx.imp ?_⟩
  intro i j hij t hti htj
  exact hij ((hbase i t hti).symm.trans (hbase j t htj))

theorem clone_list_toFinset [Fintype α] (xs : List α) (hfull : ∀ i, i ∈ xs)
    (positions : α → List σ) :
    (xs.flatMap positions).toFinset = Finset.univ.biUnion (fun i => (positions i).toFinset) := by
  ext t
  simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  exact ⟨fun ⟨i, _, ht⟩ => ⟨i, ht⟩, fun ⟨i, ht⟩ => ⟨i, hfull i, ht⟩⟩

theorem phi_clone_multidegree [Fintype α] (xs : List α) (hx : xs.Nodup)
    (hfull : ∀ i, i ∈ xs) (positions : α → List σ) (hp : ∀ i, (positions i).Nodup)
    (base : σ → α) (hbase : ∀ i, ∀ j ∈ positions i, base j = i)
    (v : List α) (hv : ∀ i, v.count i = (positions i).length) :
    BCHPhi.phi (fun j => letter (base ((xs.flatMap positions).get j))) =
      (∏ i : α, ((positions i).length.factorial : ℚ)) •
        selectWords v (logCoefficient (wordSeries (xs.map letter)) (xs.flatMap positions).length) := by
  have hnodup := clone_list_nodup xs hx positions hp base hbase
  have hd := clone_blocks_disjoint positions base hbase
  have hset := clone_list_toFinset xs hfull positions
  have hcounts : wordCounts (xs.flatMap positions) =
      squarefree (Finset.univ.biUnion (fun i => (positions i).toFinset)) := by
    rw [wordCounts_eq_squarefree _ hnodup, hset]
  have hcard (i : α) : (positions i).toFinset.card = (positions i).length :=
    List.toFinset_card_of_nodup (hp i)
  have hr : (fun i => ((positions i).map
      (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).sum) =
      (fun i => ∑ j ∈ (positions i).toFinset, (MvPolynomial.X j : MvPolynomial σ ℚ)) := by
    funext i
    exact (List.sum_toFinset _ (hp i)).symm
  have hc := BCHPolarWord.evaluate_log_clone_blocks xs positions base hbase
    (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ)) (fun i => (polarLetter i : PolarAlg σ α))
    (xs.flatMap positions).length
  change tagWords base (logCoefficient (wordSeries ((xs.flatMap positions).map letter))
      (xs.flatMap positions).length) =
    scaleWords (fun i => ((positions i).map
      (fun j => (MvPolynomial.X j : MvPolynomial σ ℚ))).sum)
      (logCoefficient (wordSeries (xs.map letter)) (xs.flatMap positions).length) at hc
  rw [hr] at hc
  rw [← evaluate_selected_log_list (fun j => letter (base j)) _ hnodup,
    ← extract_tagWords, hcounts, hc,
    extract_scaleWords (fun i => (positions i).toFinset) hd v
      (fun i => (hv i).trans (hcard i).symm)]
  simp only [hcard]

theorem log_multidegree_eq_phi [Fintype α] (xs : List α) (hx : xs.Nodup)
    (hfull : ∀ i, i ∈ xs) (positions : α → List σ) (hp : ∀ i, (positions i).Nodup)
    (base : σ → α) (hbase : ∀ i, ∀ j ∈ positions i, base j = i)
    (v : List α) (hv : ∀ i, v.count i = (positions i).length) :
    selectWords v (logCoefficient (wordSeries (xs.map letter)) (xs.flatMap positions).length) =
      (∏ i : α, ((positions i).length.factorial : ℚ))⁻¹ •
        BCHPhi.phi (fun j => letter (base ((xs.flatMap positions).get j))) := by
  rw [phi_clone_multidegree xs hx hfull positions hp base hbase v hv, smul_smul,
    inv_mul_cancel₀, one_smul]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (positions i).length

theorem evaluate_log_multidegree_eq_phi {B : Type} [Ring B] [Algebra ℚ B] [Fintype α]
    (X : α → B) (xs : List α) (hx : xs.Nodup) (hfull : ∀ i, i ∈ xs)
    (positions : α → List σ) (hp : ∀ i, (positions i).Nodup)
    (base : σ → α) (hbase : ∀ i, ∀ j ∈ positions i, base j = i)
    (v : List α) (hv : ∀ i, v.count i = (positions i).length) :
    evaluateWords X (selectWords v
      (logCoefficient (wordSeries (xs.map letter)) (xs.flatMap positions).length)) =
        (∏ i : α, ((positions i).length.factorial : ℚ))⁻¹ •
          BCHPhi.phi (fun j => X (base ((xs.flatMap positions).get j))) := by
  rw [log_multidegree_eq_phi xs hx hfull positions hp base hbase v hv, map_smul]
  congr 1
  exact evaluate_relabel X (fun j => base ((xs.flatMap positions).get j)) _

theorem count_expanded_list (xs : List α) (hx : xs.Nodup) (m : α → ℕ) (i : α) :
    (xs.flatMap (fun a => List.replicate (m a) a)).count i = if i ∈ xs then m i else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have htail := hx.tail
    have hnot := (List.nodup_cons.mp hx).1
    by_cases hi : i = a
    · subst i
      simp [List.flatMap_cons, ih htail, hnot]
    · have hrep : (List.replicate (m a) a).count i = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        exact hi (List.mem_replicate.mp hm).2
      simp [List.flatMap_cons, ih htail, hi, hrep]

theorem evaluate_log_expanded_eq_phi {B : Type} [Ring B] [Algebra ℚ B] [Fintype α]
    (X : α → B) (xs : List α) (hx : xs.Nodup) (hfull : ∀ i, i ∈ xs)
    (positions : α → List σ) (hp : ∀ i, (positions i).Nodup)
    (base : σ → α) (hbase : ∀ i, ∀ j ∈ positions i, base j = i) :
    evaluateWords X (selectWords (xs.flatMap (fun i => List.replicate (positions i).length i))
      (logCoefficient (wordSeries (xs.map letter)) (xs.flatMap positions).length)) =
        (∏ i : α, ((positions i).length.factorial : ℚ))⁻¹ •
          BCHPhi.phi (fun j => X (base ((xs.flatMap positions).get j))) := by
  apply evaluate_log_multidegree_eq_phi X xs hx hfull positions hp base hbase
  intro i
  rw [count_expanded_list xs hx, if_pos (hfull i)]

theorem evaluate_log_sigma_multidegree {B : Type} [Ring B] [Algebra ℚ B] {Γ : ℕ}
    (X : Fin Γ → B) (m : Fin Γ → ℕ) :
    let positions := fun i => List.ofFn
      (fun j : Fin (m i) => (⟨i, j⟩ : Σ i, Fin (m i)))
    evaluateWords X (selectWords ((List.finRange Γ).flatMap (fun i => List.replicate (m i) i))
      (logCoefficient (wordSeries ((List.finRange Γ).map letter))
        ((List.finRange Γ).flatMap positions).length)) =
      (∏ i : Fin Γ, (m i).factorial : ℚ)⁻¹ •
        BCHPhi.phi (fun j => X (((List.finRange Γ).flatMap positions).get j).1) := by
  (try dsimp only)
  have hp (i : Fin Γ) : (List.ofFn
      (fun j : Fin (m i) => (⟨i, j⟩ : Σ i, Fin (m i)))).Nodup := by
    apply List.nodup_ofFn.mpr
    intro j k h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using! h
  have hb (i : Fin Γ) (j : Σ i, Fin (m i))
      (hj : j ∈ List.ofFn (fun k : Fin (m i) => (⟨i, k⟩ : Σ i, Fin (m i)))) : j.1 = i := by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
    rfl
  simpa only [List.length_ofFn, Nat.cast_prod] using!
    evaluate_log_expanded_eq_phi X (List.finRange Γ) (List.nodup_finRange Γ)
      (List.mem_finRange) (fun i => List.ofFn
        (fun j : Fin (m i) => (⟨i, j⟩ : Σ i, Fin (m i)))) hp Sigma.fst hb

end Qatlib.Papers.CommutLCHS26.MainResults.BCHMultidegree
