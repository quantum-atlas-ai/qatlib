/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Threshold weights for independent repetition

This module defines product weights for success patterns and sums them above a success-count
threshold. It proves normalization, binomial formulas, threshold monotonicity, and
coordinatewise monotonicity for probabilities in the unit interval.

The finite-set variants `patternWeightOn` and `acceptWeightOn` support splitting off one trial
and updating individual success probabilities. See [MarriottWatrous2005].

## Main statements

* `sum_patternWeight`: the pattern weights sum to one.
* `acceptWeight_const_eq`: the constant-probability tail is a binomial sum.
* `acceptWeight_mono_coord`: increasing success probabilities increases the tail weight.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false

open Finset
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.ArxivCs0506068.ParallelRep

noncomputable section

variable {N : ℕ}

/-- The product weight of the success pattern `S`, multiplying `p i` on `S` and `1 - p i`
outside `S`. -/
def patternWeight (p : Fin N → ℝ) (S : Finset (Fin N)) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ univ \ S, (1 - p i)

/-- The sum of product-pattern weights for patterns with at least `T` successes. -/
def acceptWeight (p : Fin N → ℝ) (T : ℕ) : ℝ :=
  ∑ S ∈ univ.powerset.filter (fun S => T ≤ S.card), patternWeight p S

/-- The weights of all success patterns sum to one. See [Marriott and Watrous, Theorem
4.2][MarriottWatrous2005]. -/
theorem sum_patternWeight (p : Fin N → ℝ) :
    (∑ S ∈ univ.powerset, patternWeight p S) = 1 := by
  have h := (Finset.prod_add p (fun i => 1 - p i) (univ : Finset (Fin N))).symm
  rw [show (∑ S ∈ univ.powerset, patternWeight p S)
      = ∑ S ∈ univ.powerset, (∏ i ∈ S, p i) * ∏ i ∈ univ \ S, (1 - p i) from rfl]
  rw [h]
  simp

/-- Pattern weights are nonnegative when every coordinate probability lies in the unit interval. -/
theorem patternWeight_nonneg (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (S : Finset (Fin N)) : 0 ≤ patternWeight p S := by
  unfold patternWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => hp i)
  · exact Finset.prod_nonneg (fun i _ => by linarith [hp1 i])

/-- Threshold acceptance weights are nonnegative for coordinate probabilities in the unit
interval. -/
theorem acceptWeight_nonneg (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (T : ℕ) : 0 ≤ acceptWeight p T := by
  unfold acceptWeight
  exact Finset.sum_nonneg (fun S _ => patternWeight_nonneg p hp hp1 S)

/-- Threshold acceptance weights are at most one for coordinate probabilities in the unit
interval. -/
theorem acceptWeight_le_one (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (T : ℕ) : acceptWeight p T ≤ 1 := by
  unfold acceptWeight
  calc ∑ S ∈ univ.powerset.filter (fun S => T ≤ S.card), patternWeight p S
      ≤ ∑ S ∈ univ.powerset, patternWeight p S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _
        exact patternWeight_nonneg p hp hp1 S
    _ = 1 := sum_patternWeight p

/-- Increasing the success threshold decreases the acceptance weight for probabilities in the
unit interval. See [Marriott and Watrous, Theorem 4.2][MarriottWatrous2005]. -/
theorem acceptWeight_mono_threshold (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) {T T' : ℕ} (hTT' : T' ≤ T) :
    acceptWeight p T ≤ acceptWeight p T' := by
  unfold acceptWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨hS.1, le_trans hTT' hS.2⟩
  · intro S _ _
    exact patternWeight_nonneg p hp hp1 S

/-- When every trial succeeds with weight one, acceptance weight is one exactly when the
threshold is at most `N`, and zero otherwise. -/
theorem acceptWeight_one (T : ℕ) :
    acceptWeight (fun _ : Fin N => (1 : ℝ)) T = if T ≤ N then 1 else 0 := by
  classical
  have hzero : ∀ S ∈ univ.powerset, S ≠ univ →
      patternWeight (fun _ : Fin N => (1 : ℝ)) S = 0 := by
    intro S _ hS
    have hne : (univ \ S : Finset (Fin N)).Nonempty := by
      by_contra h
      apply hS
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      exact h ⟨i, by simp [hi]⟩
    unfold patternWeight
    have hprod : (∏ i ∈ univ \ S, ((1 : ℝ) - 1)) = 0 := by
      obtain ⟨i, hi⟩ := hne
      exact Finset.prod_eq_zero hi (by norm_num)
    rw [hprod, mul_zero]
  by_cases hT : T ≤ N
  · rw [if_pos hT]
    unfold acceptWeight
    have hmem : (univ : Finset (Fin N)) ∈ (univ : Finset (Fin N)).powerset.filter (fun S => T ≤ S.card) := by
      simp [hT]
    rw [Finset.sum_eq_single (s := (univ : Finset (Fin N)).powerset.filter (fun S => T ≤ S.card)) (a := (univ : Finset (Fin N)))]
    · simp [patternWeight]
    · intro S hS hSne
      exact hzero S (Finset.mem_filter.mp hS).1 hSne
    · intro hnot
      exact absurd hmem hnot
  · rw [if_neg hT]
    unfold acceptWeight
    rw [Finset.sum_eq_zero]
    intro S hS
    have hcard : S.card ≤ N := by
      have := Finset.card_le_univ S
      simpa using this
    have hTle : T ≤ S.card := (Finset.mem_filter.mp hS).2
    exact absurd (le_trans hTle hcard) hT

/-- For constant success weight `p`, a pattern has weight `p ^ S.card * (1 - p) ^ (N - S.card)`. -/
theorem patternWeight_const (p : ℝ) (S : Finset (Fin N)) :
    patternWeight (fun _ => p) S = p ^ S.card * (1 - p) ^ (N - S.card) := by
  unfold patternWeight
  rw [Finset.prod_const, Finset.prod_const]
  have h : (univ \ S : Finset (Fin N)).card = N - S.card := by
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
    congr 1
    simp
  rw [h]

/-- For constant success weight, the threshold acceptance weight equals the corresponding
binomial tail sum. See [Marriott and Watrous, Theorem 4.2][MarriottWatrous2005]. -/
theorem acceptWeight_const_eq (p : ℝ) (T : ℕ) :
    acceptWeight (fun _ : Fin N => p) T =
      ∑ j ∈ (Finset.range (N + 1)).filter (fun j => T ≤ j),
        (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) := by
  classical
  unfold acceptWeight
  rw [Finset.sum_filter]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  have hstep : (∑ S ∈ Finset.powersetCard j Finset.univ,
      (if T ≤ S.card then patternWeight (fun _ : Fin N => p) S else 0))
      = (if T ≤ j then (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) else 0) := by
    have h : ∀ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin N)),
        (if T ≤ S.card then patternWeight (fun _ : Fin N => p) S else 0)
          = (if T ≤ j then p ^ j * (1 - p) ^ (N - j) else 0) := by
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      rw [patternWeight_const, hS.2]
    calc (∑ S ∈ Finset.powersetCard j Finset.univ,
        (if T ≤ S.card then patternWeight (fun _ : Fin N => p) S else 0))
        = ∑ _S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin N)),
            (if T ≤ j then p ^ j * (1 - p) ^ (N - j) else 0) :=
          Finset.sum_congr rfl h
      _ = (Finset.powersetCard j (Finset.univ : Finset (Fin N))).card *
            (if T ≤ j then p ^ j * (1 - p) ^ (N - j) else 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (if T ≤ j then (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) else 0) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          split_ifs with hT
          · ring
          · simp
  rw [hstep]

section General

variable {ι : Type*} [DecidableEq ι]

/-- The product weight of a pattern `S` relative to trial set `C`, with failure factors on `C`
outside `S`. -/
def patternWeightOn (C : Finset ι) (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ j ∈ S, p j) * ∏ j ∈ C \ S, (1 - p j)

/-- The total weight of subsets of `C` containing at least `T` successes. -/
def acceptWeightOn (C : Finset ι) (p : ι → ℝ) (T : ℕ) : ℝ :=
  ∑ S ∈ C.powerset.filter (fun S => T ≤ S.card), patternWeightOn C p S

/-- Finite-set pattern weights are nonnegative for coordinate probabilities in the unit
interval. -/
theorem patternWeightOn_nonneg {C : Finset ι} {p : ι → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) (S : Finset ι) : 0 ≤ patternWeightOn C p S := by
  unfold patternWeightOn
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hp i))
    (Finset.prod_nonneg (fun i _ => by linarith [hp1 i]))

/-- If `i` belongs to `C` and not to `S`, split off its failure factor `1 - p i` from the
pattern weight. -/
theorem patternWeightOn_insert {C : Finset ι} {p : ι → ℝ} {i : ι} (S : Finset ι)
    (hiC : i ∈ C) (hiS : i ∉ S) :
    patternWeightOn C p S = (1 - p i) * patternWeightOn (C.erase i) p S := by
  unfold patternWeightOn
  have hdiff : C \ S = insert i (C.erase i \ S) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxC, hxS⟩
      by_cases hx : x = i
      · exact Or.inl hx
      · exact Or.inr ⟨⟨hx, hxC⟩, hxS⟩
    · rintro (rfl | ⟨⟨hxi, hxC⟩, hxS⟩)
      · exact ⟨hiC, hiS⟩
      · exact ⟨hxC, hxS⟩
  have hni : i ∉ (C.erase i \ S) := by
    simp [Finset.mem_sdiff]
  rw [hdiff, Finset.prod_insert hni]
  ring

/-- If `i` belongs to `C` and not to `S`, the weight of `insert i S` splits off the success
factor `p i`. -/
theorem patternWeightOn_insert_insert {C : Finset ι} {p : ι → ℝ} {i : ι} (S : Finset ι)
    (hiC : i ∈ C) (hiS : i ∉ S) :
    patternWeightOn C p (insert i S) = p i * patternWeightOn (C.erase i) p S := by
  unfold patternWeightOn
  have hdiff : C \ insert i S = C.erase i \ S := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxC, hx⟩
      exact ⟨⟨fun h => hx (Or.inl h), hxC⟩, fun h => hx (Or.inr h)⟩
    · rintro ⟨⟨hxi, hxC⟩, hxS⟩
      exact ⟨hxC, by rintro (rfl | h) <;> contradiction⟩
  rw [hdiff, Finset.prod_insert hiS]
  ring

/-- Split the acceptance weight after inserting a new trial into its failure and success
contributions. -/
theorem acceptWeightOn_insert {C : Finset ι} {p : ι → ℝ} {i : ι} (hi : i ∉ C) (T : ℕ) :
    acceptWeightOn (insert i C) p T = (1 - p i) *
        (∑ t ∈ C.powerset, if T ≤ t.card then patternWeightOn C p t else 0)
      + p i * (∑ t ∈ C.powerset, if T ≤ t.card + 1 then patternWeightOn C p t else 0) := by
  classical
  unfold acceptWeightOn
  rw [Finset.sum_filter, Finset.sum_powerset_insert hi]
  have h1 : ∀ t ∈ C.powerset,
      (if T ≤ t.card then patternWeightOn (insert i C) p t else 0)
        = (1 - p i) * (if T ≤ t.card then patternWeightOn C p t else 0) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have hit : i ∉ t := fun h => hi (ht h)
    rw [patternWeightOn_insert t (Finset.mem_insert_self i C) hit, Finset.erase_insert hi]
    split_ifs <;> ring
  have h2 : ∀ t ∈ C.powerset,
      (if T ≤ (insert i t).card then patternWeightOn (insert i C) p (insert i t) else 0)
        = p i * (if T ≤ t.card + 1 then patternWeightOn C p t else 0) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have hit : i ∉ t := fun h => hi (ht h)
    rw [patternWeightOn_insert_insert t (Finset.mem_insert_self i C) hit, Finset.erase_insert hi,
      Finset.card_insert_of_notMem hit]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.mul_sum, Finset.mul_sum]

/-- Split acceptance weight at an existing trial using patterns on the set with that trial
erased. -/
theorem acceptWeightOn_eq_split {C : Finset ι} {p : ι → ℝ} {i : ι} (hiC : i ∈ C) (T : ℕ) :
    acceptWeightOn C p T = (1 - p i) *
        (∑ t ∈ (C.erase i).powerset, if T ≤ t.card then patternWeightOn (C.erase i) p t else 0)
      + p i * (∑ t ∈ (C.erase i).powerset,
          if T ≤ t.card + 1 then patternWeightOn (C.erase i) p t else 0) := by
  have h := acceptWeightOn_insert (C := C.erase i) (p := p) (i := i)
    (Finset.notMem_erase i C) T
  rwa [Finset.insert_erase hiC] at h

/-- Pattern weights agree when the coordinate functions agree on `C` and `S` is contained in
`C`. -/
theorem patternWeightOn_congr {C : Finset ι} {p q : ι → ℝ} (h : ∀ j ∈ C, p j = q j)
    {S : Finset ι} (hS : S ⊆ C) : patternWeightOn C p S = patternWeightOn C q S := by
  unfold patternWeightOn
  congr 1
  · exact Finset.prod_congr rfl (fun j hj => h j (hS hj))
  · exact Finset.prod_congr rfl (fun j hj => by rw [h j (Finset.mem_sdiff.mp hj).1])

/-- Increasing the threshold decreases the finite-set acceptance weight for probabilities in the
unit interval. -/
theorem acceptWeightOn_mono_threshold {C : Finset ι} {p : ι → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∀ j, p j ≤ 1) {T T' : ℕ} (h : T' ≤ T) :
    acceptWeightOn C p T ≤ acceptWeightOn C p T' := by
  unfold acceptWeightOn
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    simp only [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, le_trans h hS.2⟩
  · intro S _ _; exact patternWeightOn_nonneg hp hp1 S

/-- The sum of pattern weights on `C` for which one additional success would reach threshold
`T`. -/
def lowWeightOn (C : Finset ι) (p : ι → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ C.powerset, if T ≤ t.card + 1 then patternWeightOn C p t else 0

/-- Express finite-set acceptance weight as a sum over all subsets with a threshold indicator. -/
theorem acceptWeightOn_eq_sum_if (C : Finset ι) (p : ι → ℝ) (T : ℕ) :
    acceptWeightOn C p T = ∑ t ∈ C.powerset, if T ≤ t.card then patternWeightOn C p t else 0 := by
  unfold acceptWeightOn
  rw [Finset.sum_filter]

/-- The weight requiring one additional success equals acceptance weight at the truncated
threshold `T - 1`. -/
theorem lowWeightOn_eq (C : Finset ι) (p : ι → ℝ) (T : ℕ) :
    lowWeightOn C p T = acceptWeightOn C p (T - 1) := by
  unfold lowWeightOn
  rw [acceptWeightOn_eq_sum_if]
  apply Finset.sum_congr rfl
  intro t _
  have h : (T ≤ t.card + 1) ↔ (T - 1 ≤ t.card) := by omega
  by_cases hT : T ≤ t.card + 1
  · rw [if_pos hT, if_pos (h.mp hT)]
  · rw [if_neg hT, if_neg (fun hc => hT (h.mpr hc))]

/-- Adding a fresh trial expresses acceptance as `(1 - p i)` times the old tail plus `p i` times
the tail at threshold `T - 1`. -/
theorem acceptWeightOn_insert_low {C : Finset ι} {p : ι → ℝ} {i : ι} (hi : i ∉ C) (T : ℕ) :
    acceptWeightOn (insert i C) p T = (1 - p i) * acceptWeightOn C p T + p i * acceptWeightOn C p (T - 1) := by
  rw [acceptWeightOn_insert hi T, acceptWeightOn_eq_sum_if]
  have h2 : (∑ t ∈ C.powerset, if T ≤ t.card + 1 then patternWeightOn C p t else 0)
      = acceptWeightOn C p (T - 1) := lowWeightOn_eq C p T
  rw [h2]

/-- Increasing the success weight of a newly inserted trial cannot decrease acceptance when the
original coordinate probabilities lie in the unit interval. -/
theorem acceptWeightOn_update_le {C : Finset ι} {p : ι → ℝ} {i : ι} (hi : i ∉ C)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (x : ℝ) (hx : p i ≤ x)
    (T : ℕ) :
    acceptWeightOn (insert i C) p T ≤ acceptWeightOn (insert i C) (Function.update p i x) T := by
  have hupd : Function.update p i x i = x := Function.update_self i _ p
  have hcongr : ∀ j ∈ C, Function.update p i x j = p j := by
    intro j hj
    exact Function.update_of_ne (fun (h : j = i) => hi (by rw [← h]; exact hj)) _ p
  have hpx : ∀ j, 0 ≤ Function.update p i x j := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hupd]; linarith [hp j]
    · rw [Function.update_of_ne hj]; exact hp j
  have hY : acceptWeightOn C (Function.update p i x) T = acceptWeightOn C p T := by
    unfold acceptWeightOn
    exact Finset.sum_congr rfl (fun t ht => by
      rw [patternWeightOn_congr (fun j hj => hcongr j hj)
        (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1)])
  have hX : acceptWeightOn C (Function.update p i x) (T - 1) = acceptWeightOn C p (T - 1) := by
    unfold acceptWeightOn
    exact Finset.sum_congr rfl (fun t ht => by
      rw [patternWeightOn_congr (fun j hj => hcongr j hj)
        (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1)])
  rw [acceptWeightOn_insert_low hi T, acceptWeightOn_insert_low hi T, hupd, hY, hX]
  have hmono : acceptWeightOn C p T ≤ acceptWeightOn C p (T - 1) :=
      acceptWeightOn_mono_threshold hp hp1 (Nat.sub_le T 1)
  nlinarith [hmono]

/-- Finite-set acceptance weight increases when unit-interval probabilities increase on `C` and
agree outside `C`. -/
theorem acceptWeightOn_le_of_le_on (C : Finset ι) (p q : ι → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hq : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hle : ∀ j ∈ C, p j ≤ q j) (heq : ∀ j ∉ C, p j = q j) (T : ℕ) :
    acceptWeightOn C p T ≤ acceptWeightOn C q T := by
  classical
  have key : ∀ (C : Finset ι) (p q : ι → ℝ),
      (∀ j, 0 ≤ p j) → (∀ j, p j ≤ 1) →
      (∀ j, 0 ≤ q j) → (∀ j, q j ≤ 1) →
      (∀ j ∈ C, p j ≤ q j) → (∀ j ∉ C, p j = q j) →
      ∀ T, acceptWeightOn C p T ≤ acceptWeightOn C q T := by
    intro C
    induction C using Finset.induction_on with
    | empty =>
        intro p q hp hp1 hq hq1 hle heq T
        have hval : ∀ r : ι → ℝ, acceptWeightOn ∅ r T = (if T ≤ 0 then 1 else 0) := by
          intro r
          unfold acceptWeightOn
          rw [Finset.powerset_empty, Finset.sum_filter, Finset.sum_singleton]
          simp only [Finset.card_empty]
          by_cases hT : T ≤ 0
          · rw [if_pos hT, if_pos hT]; simp [patternWeightOn]
          · rw [if_neg hT, if_neg hT]
        rw [hval p, hval q]
    | insert a s ha ih =>
        intro p q hp hp1 hq hq1 hle heq T
        have hleS : ∀ j ∈ s, p j ≤ q j := fun j hj => hle j (Finset.mem_insert_of_mem hj)
        have heqS : ∀ j ∉ s, Function.update p a (q a) j = q j := by
          intro j hj
          by_cases hja : j = a
          · rw [hja]; exact Function.update_self a _ p
          · rw [Function.update_of_ne hja]
            exact heq j (fun h => by
              rcases Finset.mem_insert.mp h with h' | h'
              · exact hja h'
              · exact hj h')
        have hr0 : ∀ j, 0 ≤ Function.update p a (q a) j := by
          intro j
          by_cases hja : j = a
          · rw [hja, Function.update_self]; exact hq a
          · rw [Function.update_of_ne hja]; exact hp j
        have hr1 : ∀ j, Function.update p a (q a) j ≤ 1 := by
          intro j
          by_cases hja : j = a
          · rw [hja, Function.update_self]; exact hq1 a
          · rw [Function.update_of_ne hja]; exact hp1 j
        have hrle : ∀ j ∈ s, Function.update p a (q a) j ≤ q j := by
          intro j hj
          rw [Function.update_of_ne (fun (h : j = a) => ha (by rw [← h]; exact hj))]
          exact hleS j hj
        have hstep1 : acceptWeightOn (insert a s) p T ≤
            acceptWeightOn (insert a s) (Function.update p a (q a)) T :=
          acceptWeightOn_update_le ha hp hp1 (q a) (hle a (Finset.mem_insert_self a s)) T
        have hIH1 := ih (Function.update p a (q a)) q hr0 hr1 hq hq1 hrle heqS T
        have hIH2 := ih (Function.update p a (q a)) q hr0 hr1 hq hq1 hrle heqS (T - 1)
        have hra : Function.update p a (q a) a = q a := Function.update_self a _ p
        have hS1 : acceptWeightOn (insert a s) (Function.update p a (q a)) T
            = (1 - q a) * acceptWeightOn s (Function.update p a (q a)) T
              + q a * acceptWeightOn s (Function.update p a (q a)) (T - 1) := by
          rw [acceptWeightOn_insert_low ha T, hra]
        have hQ1 : acceptWeightOn (insert a s) q T
            = (1 - q a) * acceptWeightOn s q T + q a * acceptWeightOn s q (T - 1) := acceptWeightOn_insert_low ha T
        rw [hS1] at hstep1
        rw [hQ1]
        nlinarith [hstep1, hIH1, hIH2, hq a, hq1 a]
  exact key C p q hp hp1 hq hq1 hle heq T

end General

/-- Acceptance weight on the universal finite set agrees with `acceptWeight`. -/
theorem acceptWeightOn_univ (p : Fin N → ℝ) (T : ℕ) :
    acceptWeightOn (univ : Finset (Fin N)) p T = acceptWeight p T := rfl

/-- Coordinatewise increases of unit-interval success probabilities increase the threshold
acceptance weight. See [Marriott and Watrous, Theorem 4.2][MarriottWatrous2005]. -/
theorem acceptWeight_mono_coord (p q : Fin N → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hq : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (h : ∀ j, p j ≤ q j) (T : ℕ) :
    acceptWeight p T ≤ acceptWeight q T := by
  rw [← acceptWeightOn_univ p T, ← acceptWeightOn_univ q T]
  exact acceptWeightOn_le_of_le_on (univ : Finset (Fin N)) p q hp hp1 hq hq1
    (fun j _ => h j) (fun j hj => absurd hj (by simp)) T

/-- An upper bound on each coordinate probability gives an upper bound on the threshold
acceptance weight. -/
theorem acceptWeight_le_top (p top : Fin N → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (ht : ∀ j, 0 ≤ top j) (ht1 : ∀ j, top j ≤ 1)
    (h : ∀ j, p j ≤ top j) (T : ℕ) :
    acceptWeight p T ≤ acceptWeight top T :=
  acceptWeight_mono_coord p top hp hp1 ht ht1 h T

end

end Qatlib.Papers.ArxivCs0506068.ParallelRep
