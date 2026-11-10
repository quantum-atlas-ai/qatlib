/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHCutCounts
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Perm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHMultilinear

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordLie BCHWordCuts BCHCutCounts BCHEulerian
variable {α : Type}

def permutationWords (xs : List α) : Finset (List α) := by
  classical
  exact xs.permutations.toFinset

theorem mem_permutationWords (w xs : List α) : w ∈ permutationWords xs ↔ w.Perm xs := by
  simp only [permutationWords, List.mem_toFinset, List.mem_permutations]

theorem sum_permutationWords_list {M : Type} [AddCommMonoid M] (xs : List α)
    (hxs : xs.Nodup) (f : List α → M) :
    (∑ w ∈ permutationWords xs, f w) = (xs.permutations.map f).sum := by
  classical
  change xs.permutations.toFinset.sum f = _
  exact List.sum_toFinset f (List.nodup_permutations xs hxs)

def selectWords (xs : List α) : WordAlg α →ₗ[ℚ] WordAlg α := by
  classical
  exact
    { toFun := fun p => MonoidAlgebra.ofCoeff (p.coeff.filter (fun w => w.toList.Perm xs))
      map_add' := by
        intro p q
        apply MonoidAlgebra.coeff_injective
        apply Finsupp.ext
        intro w
        simp only [MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply,
          MonoidAlgebra.coeff_add, Finsupp.add_apply]
        split_ifs <;> simp only [add_zero]
      map_smul' := by
        intro c p
        apply MonoidAlgebra.coeff_injective
        apply Finsupp.ext
        intro w
        simp only [MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply,
          MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
        by_cases h : w.toList.Perm xs
        · simp only [if_pos h]
          rfl
        · simp only [if_neg h, mul_zero]
        }

theorem selectWords_coeff (xs : List α) (p : WordAlg α) (w : FreeMonoid α) :
    (selectWords xs p).coeff w = if w.toList.Perm xs then p.coeff w else 0 := by
  classical
  rfl

theorem word_coeff (u : List α) (v : FreeMonoid α) :
    (word u).coeff v = if u = v.toList then 1 else 0 := by
  classical
  change MonoidAlgebra.single (FreeMonoid.ofList u) 1 v = _
  rw [MonoidAlgebra.single_apply]
  by_cases h : u = v.toList
  · have he : FreeMonoid.ofList u = v := by simpa only [FreeMonoid.ofList_toList] using congrArg FreeMonoid.ofList h
    rw [if_pos h, if_pos he]
  · have he : FreeMonoid.ofList u ≠ v := by
      intro he
      exact h (by simpa only [FreeMonoid.toList_ofList] using congrArg FreeMonoid.toList he)
    rw [if_neg h, if_neg he]

def SupportedOn (p : WordAlg α) (xs : List α) : Prop := ∀ w ∈ p.support, w.toList.Perm xs

theorem supportedOn_word (xs : List α) : SupportedOn (word xs) xs := by
  intro v hv
  have hn : (word xs).coeff v ≠ 0 := by simpa using! hv
  rw [word_coeff] at hn
  have he : xs = v.toList := by split_ifs at hn with h; exact h; contradiction
  simpa only [he] using List.Perm.refl xs

theorem SupportedOn.sub {p q : WordAlg α} {xs : List α}
    (hp : SupportedOn p xs) (hq : SupportedOn q xs) : SupportedOn (p - q) xs := by
  intro v hv
  by_cases h : p.coeff v = 0
  · apply hq v
    have hn : (p - q).coeff v ≠ 0 := by simpa using! hv
    have hq' : q.coeff v ≠ 0 := by
      intro he
      apply hn
      simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, h, he, sub_zero]
    simpa using! hq'
  · exact hp v (by simpa using! h)

theorem SupportedOn.mul {p q : WordAlg α} {xs ys : List α}
    (hp : SupportedOn p xs) (hq : SupportedOn q ys) : SupportedOn (p * q) (xs ++ ys) := by
  classical
  intro v hv
  have hn : (p * q).coeff (FreeMonoid.ofList v.toList) ≠ 0 := by simpa using! hv
  rw [wordCoeff_mul] at hn
  obtain ⟨i, hi, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hleft := (mul_ne_zero_iff.mp hprod).1
  have hright := (mul_ne_zero_iff.mp hprod).2
  have hl := hp (FreeMonoid.ofList (v.toList.take i)) (by simpa using! hleft)
  have hr := hq (FreeMonoid.ofList (v.toList.drop i)) (by simpa using! hright)
  simpa only [FreeMonoid.toList_ofList, List.take_append_drop] using hl.append hr

theorem supportedOn_rightBracket (xs : List α) : SupportedOn (rightBracket (xs.map letter)) xs := by
  induction xs with
  | nil =>
    change SupportedOn (0 : WordAlg α) []
    intro v hv
    have hn := Finsupp.mem_support_iff.mp hv
    exact False.elim (hn rfl)
  | cons a xs ih =>
    have ha : letter a = word [a] := by simp [letter, word]
    cases xs with
    | nil => simpa only [List.map_cons, List.map_nil, rightBracket, ha] using supportedOn_word [a]
    | cons b xs =>
      simp only [List.map_cons, rightBracket]
      apply SupportedOn.sub
      · simpa only [ha, List.singleton_append] using! (supportedOn_word [a]).mul ih
      · intro v hv
        have he := (ih.mul (supportedOn_word [a])) v (by simpa only [ha] using! hv)
        exact he.trans List.perm_append_comm

theorem selectWords_eq_self {xs : List α} (p : WordAlg α) (hp : SupportedOn p xs) :
    selectWords xs p = p := by
  classical
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro v
  rw [selectWords_coeff]
  by_cases h : v.toList.Perm xs
  · rw [if_pos h]
  · rw [if_neg h]
    symm
    by_contra he
    exact h (hp v (by simpa using! he))

theorem selectWords_eq_zero {xs ys : List α} (p : WordAlg α) (hp : SupportedOn p ys)
    (hxy : ¬ ys.Perm xs) : selectWords xs p = 0 := by
  classical
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro v
  rw [selectWords_coeff]
  by_cases h : v.toList.Perm xs
  · rw [if_pos h]
    by_contra he
    have hpv := hp v (by simpa using! he)
    exact hxy (hpv.symm.trans h)
  · rw [if_neg h]
    rfl

theorem selectWords_rightBracket (xs w : List α) :
    selectWords xs (rightBracket (w.map letter)) =
      if w.Perm xs then rightBracket (w.map letter) else 0 := by
  classical
  by_cases h : w.Perm xs
  · rw [if_pos h]
    apply selectWords_eq_self
    intro v hv
    exact (supportedOn_rightBracket w v hv).trans h
  · rw [if_neg h]
    exact selectWords_eq_zero _ (supportedOn_rightBracket w) h

theorem selectWords_word (xs w : List α) :
    selectWords xs (word w) = if w.Perm xs then word w else 0 := by
  by_cases h : w.Perm xs
  · rw [if_pos h]
    apply selectWords_eq_self
    intro v hv
    exact (supportedOn_word w v hv).trans h
  · rw [if_neg h]
    exact selectWords_eq_zero _ (supportedOn_word w) h

theorem dynkin_word (w : List α) : dynkin (word w) = rightBracket (w.map letter) := by
  rw [word, dynkin_single]
  simp only [one_smul, FreeMonoid.toList_ofList]

theorem selectWords_dynkin (xs : List α) (p : WordAlg α) :
    selectWords xs (dynkin p) = dynkin (selectWords xs p) := by
  have hw (w : List α) : selectWords xs (dynkin (word w)) = dynkin (selectWords xs (word w)) := by
    rw [dynkin_word, selectWords_rightBracket, selectWords_word]
    by_cases h : w.Perm xs <;> simp only [h, ↓reduceIte, dynkin_word, map_zero]
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word, FreeMonoid.ofList_toList] using! hw w.toList
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul c p hp => simp only [map_smul, hp]

theorem selectWords_sum (xs : List α) (p : WordAlg α) :
    selectWords xs p = ∑ w ∈ permutationWords xs,
      p.coeff (FreeMonoid.ofList w) • word w := by
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro v
  rw [selectWords_coeff]
  unfold permutationWords
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, word_coeff, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', List.mem_toFinset, List.mem_permutations, FreeMonoid.ofList_toList]

theorem word_log_dynkin (xs : List α) (n : ℕ) :
    dynkin (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) n) =
      n • BCHWordLog.logCoefficient (wordSeries (xs.map letter)) n := by
  simpa only [letterWord, List.map_map, Function.comp_def, one_smul] using
    letterWord_log_dynkin (xs.map (fun a => ((1 : ℚ), a))) n

theorem selected_log_bracket_sum (xs : List α) (n : ℕ) (hn : 0 < n) :
    selectWords xs (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) n) =
      ∑ w ∈ permutationWords xs,
        ((BCHWordLog.logCoefficient (wordSeries (xs.map letter)) n).coeff
          (FreeMonoid.ofList w) / (n : ℚ)) • rightBracket (w.map letter) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  let p := BCHWordLog.logCoefficient (wordSeries (xs.map letter)) n
  have he : selectWords xs p = (n : ℚ)⁻¹ • dynkin (selectWords xs p) := by
    rw [← selectWords_dynkin, word_log_dynkin, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, inv_mul_cancel₀ hn0, one_smul]
  conv_lhs => change selectWords xs p; rw [he]
  rw [selectWords_sum, map_sum, Finset.smul_sum]
  simp only [map_smul, dynkin_word, smul_smul, div_eq_mul_inv, mul_comm, p]

section Ordered
variable [LinearOrder α]

theorem selected_log_phi (xs : List α) (hxs : xs.Pairwise (· < ·)) (hn : 0 < xs.length) :
    selectWords xs (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) xs.length) =
      ∑ w ∈ permutationWords xs, phiWeight xs.length (descents w) •
        rightBracket (w.map letter) := by
  rw [selected_log_bracket_sum xs xs.length hn]
  apply Finset.sum_congr rfl
  intro w hw
  have hp : w.Perm xs := (mem_permutationWords w xs).mp hw
  have hwd : w.Nodup := hp.nodup_iff.mpr hxs.nodup
  have hsub : w ⊆ xs := fun _ h => hp.mem_iff.mp h
  cases w with
  | nil => have hlen := hp.length_eq; simp only [List.length_nil] at hlen; omega
  | cons a w =>
    have hc : (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) xs.length).coeff
        (FreeMonoid.ofList (a :: w)) = descentWeight xs.length (descents (a :: w)) := by
      simpa only [hp.length_eq, descentWeight] using word_log_eulerian xs hxs a w hwd hsub
    rw [hc, descentWeight_div_degree]

theorem evaluate_selected_log_phi {B : Type} [Ring B] [Algebra ℚ B]
    (X : α → B) (xs : List α) (hxs : xs.Pairwise (· < ·)) (hn : 0 < xs.length) :
    evaluateWords X (selectWords xs (BCHWordLog.logCoefficient (wordSeries (xs.map letter)) xs.length)) =
      ∑ w ∈ permutationWords xs, phiWeight xs.length (descents w) • rightBracket (w.map X) := by
  rw [selected_log_phi xs hxs hn, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_smul, evaluateWords_rightBracket]

end Ordered

theorem ofFn_mem_permutationWords {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    List.ofFn σ ∈ permutationWords (List.finRange n) := by
  apply (mem_permutationWords _ _).mpr
  simpa only [List.ofFn_eq_map] using σ.map_finRange_perm

theorem permutation_of_word {n : ℕ} (w : List (Fin n))
    (hw : w ∈ permutationWords (List.finRange n)) : ∃ σ : Equiv.Perm (Fin n), List.ofFn σ = w := by
  have hp := (mem_permutationWords w _).mp hw
  have hlen : w.length = n := by simpa only [List.length_finRange] using hp.length_eq
  have hnd : w.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  have hmem : ∀ a : Fin n, a ∈ w := fun a => hp.mem_iff.mpr (List.mem_finRange a)
  let E := List.Nodup.getEquivOfForallMemList w hnd hmem
  let σ : Equiv.Perm (Fin n) := (finCongr hlen.symm).trans E
  refine ⟨σ, ?_⟩
  apply List.ext_getElem (by simpa only [List.length_ofFn] using hlen.symm)
  intro i hi hj
  simp only [List.getElem_ofFn]
  rfl

theorem sum_permutationWords {n : ℕ} {M : Type} [AddCommMonoid M] (f : List (Fin n) → M) :
    (∑ w ∈ permutationWords (List.finRange n), f w) = ∑ σ : Equiv.Perm (Fin n), f (List.ofFn σ) := by
  symm
  refine Finset.sum_bij (fun σ _ => List.ofFn σ) (fun σ _ => ofFn_mem_permutationWords σ) ?_ ?_ ?_
  · intro σ _ τ _ h
    exact Equiv.ext (fun i => congrFun (List.ofFn_injective h) i)
  · intro w hw
    obtain ⟨σ, hσ⟩ := permutation_of_word w hw
    exact ⟨σ, Finset.mem_univ σ, hσ⟩
  · intro σ _
    rfl

end Qatlib.Papers.CommutLCHS26.MainResults.BCHMultilinear
