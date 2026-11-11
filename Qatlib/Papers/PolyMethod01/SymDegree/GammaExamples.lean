/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyMethod01.SymDegree.SymmetricBandCost
import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
import Qatlib.Papers.PolyMethod01.MajorityBounds.MajorityExactDegree

/-!
# Jump parameters for OR and majority

The layer values and changes of OR and strict majority determine their parameter `Gamma`. For
positive dimension OR has parameter `n - 1`, while strict majority has parameter one in positive
even dimension and zero in odd dimension. These constructions support the symmetric-function
analysis of [BealsEtAl2001].

## Main statements

* `gamma_orValue`: For positive `n`, the jump parameter of OR is `n - 1`.
* `gamma_majority_even`: For positive `m`, strict majority on `2 * m` bits has jump parameter
  one.
* `gamma_majority_odd`: Strict majority on `2 * m + 1` bits has jump parameter zero.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.SymDegree

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
open scoped Classical BigOperators

variable {n : ℕ}

/-- Boolean OR is true exactly when the Hamming weight is at least one. -/
theorem orValue_eq_decide (w : Fin n → Bool) :
    orValue w = decide (1 ≤ boolWeight w) := by
  classical
  by_cases h : ∃ i, w i = true
  · have hpos : 0 < (Finset.univ.filter (fun i => w i = true)).card := by
      obtain ⟨i, hi⟩ := h
      exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    simp [orValue, boolWeight, boolSupp, h, Nat.succ_le_of_lt hpos]
  · have hzero : (Finset.univ.filter (fun i => w i = true)).card = 0 := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      exact h ⟨i, (Finset.mem_filter.mp hi).2⟩
    simp [orValue, boolWeight, boolSupp, h, hzero]

/-- Boolean OR is symmetric, depending only on Hamming weight. -/
theorem orValue_symmetric : Symmetric (@orValue n) := by
  intro x y hxy
  rw [orValue_eq_decide x, orValue_eq_decide y, hxy]

/-- Boolean OR is nonconstant when there is at least one input bit. -/
theorem orValue_nonconstant (hn : 1 ≤ n) : Nonconstant (@orValue n) := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  have h0 : orValue (fun _ : Fin n => true) = true := by
    unfold orValue
    rw [decide_eq_true_eq]
    exact ⟨⟨0, by omega⟩, rfl⟩
  have h1 : orValue (fun _ : Fin n => false) = false := by
    simp [orValue]
  rw [h0, h1]
  simp

/-- On a valid weight layer `k`, the OR layer value is the Boolean indicator of `1 ≤ k`. -/
theorem layerVal_orValue {k : ℕ} (hk : k ≤ n) :
    layerVal (@orValue n) k = decide (1 ≤ k) := by
  classical
  unfold layerVal
  rw [dif_pos hk]
  have hspec := Classical.choose_spec (exists_word_weight (n := n) (k := k) hk)
  rw [orValue_eq_decide, hspec]

/-- For `k < n`, OR changes between layers `k` and `k + 1` exactly when `k = 0`. -/
theorem layerChange_orValue_iff {k : ℕ} (hk : k < n) :
    LayerChange (@orValue n) k ↔ k = 0 := by
  rw [layerChange_iff orValue_symmetric hk, layerVal_orValue (by omega),
    layerVal_orValue (by omega)]
  by_cases h0 : k = 0
  · subst h0
    simp
  · have hk1 : 1 ≤ k := by omega
    have hk1' : 1 ≤ k + 1 := by omega
    rw [decide_eq_true_eq.mpr hk1, decide_eq_true_eq.mpr hk1']
    simp [h0]

/-- For positive `n`, the jump parameter of OR is `n - 1`. See [Beals et al.,
2001][BealsEtAl2001]. -/
theorem gamma_orValue (hn : 1 ≤ n) : Gamma (@orValue n) = n - 1 := by
  have hle : Gamma (@orValue n) ≤ n - 1 := by
    have hc : LayerChange (@orValue n) 0 :=
      (layerChange_orValue_iff (by omega)).mpr rfl
    have hgl := gamma_le_of_layerChange (f := @orValue n) (k := 0) (by omega) hc
    have hdist : Nat.dist (2 * 0 + 1) n = n - 1 := by
      show Nat.dist 1 n = n - 1
      rw [Nat.dist_eq_sub_of_le hn]
    rw [hdist] at hgl
    exact hgl
  have hge : n - 1 ≤ Gamma (@orValue n) := by
    obtain ⟨k, hk, hc, hd⟩ := gamma_mem orValue_symmetric (orValue_nonconstant hn)
    have hk0 : k = 0 := (layerChange_orValue_iff hk).mp hc
    subst hk0
    have hdist : Nat.dist (2 * 0 + 1) n = n - 1 := by
      show Nat.dist 1 n = n - 1
      rw [Nat.dist_eq_sub_of_le hn]
    rw [hd, hdist]
  omega

/-- Strict majority is symmetric, depending only on Hamming weight. -/
theorem majorityValue_symmetric : Symmetric (MajorityBounds.majorityValue (n := n)) := by
  intro x y hxy
  have hxy' : (Finset.univ.filter (fun i => x i = true)).card =
      (Finset.univ.filter (fun i => y i = true)).card := by
    simpa [boolWeight, boolSupp] using! hxy
  simp [MajorityBounds.majorityValue, hxy']

/-- Strict majority is nonconstant for positive input size. -/
theorem majorityValue_nonconstant (hn : 1 ≤ n) :
    Nonconstant (MajorityBounds.majorityValue (n := n)) := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  have h0 : MajorityBounds.majorityValue (fun _ : Fin n => true) = true := by
    simp only [MajorityBounds.majorityValue, decide_eq_true_eq]
    simp
    omega
  have h1 : MajorityBounds.majorityValue (fun _ : Fin n => false) = false := by
    simp [MajorityBounds.majorityValue]
  rw [h0, h1]
  simp

/-- On a valid weight layer `k`, strict majority has value given by the Boolean indicator of `n
< 2 * k`. -/
theorem layerVal_majority {k : ℕ} (hk : k ≤ n) :
    layerVal (MajorityBounds.majorityValue (n := n)) k = decide (n < 2 * k) := by
  classical
  unfold layerVal
  rw [dif_pos hk]
  have hspec := Classical.choose_spec (exists_word_weight (n := n) (k := k) hk)
  have hcard :
      (Finset.univ.filter (fun i =>
        Classical.choose (exists_word_weight (n := n) (k := k) hk) i = true)).card = k := by
    simpa [boolWeight, boolSupp] using! hspec
  simp only [MajorityBounds.majorityValue]
  rw [hcard]

/-- For `k < n`, strict majority changes between layers `k` and `k + 1` exactly when `2 * k = n`
or `2 * k + 1 = n`. -/
theorem layerChange_majority_iff {k : ℕ} (hk : k < n) :
    LayerChange (MajorityBounds.majorityValue (n := n)) k ↔ 2 * k = n ∨ 2 * k + 1 = n := by
  rw [layerChange_iff majorityValue_symmetric hk, layerVal_majority (by omega),
    layerVal_majority (by omega)]
  by_cases h2 : n < 2 * k
  · have h2' : n < 2 * (k + 1) := by omega
    rw [decide_eq_true_eq.mpr h2, decide_eq_true_eq.mpr h2']
    simp
    omega
  · by_cases h2' : n < 2 * (k + 1)
    · rw [decide_eq_false_iff_not.mpr h2, decide_eq_true_eq.mpr h2']
      simp
      omega
    · rw [decide_eq_false_iff_not.mpr h2, decide_eq_false_iff_not.mpr h2']
      simp
      omega

/-- For positive `m`, strict majority on `2 * m` bits has jump parameter one. See [Beals et al.,
2001][BealsEtAl2001]. -/
theorem gamma_majority_even {m : ℕ} (hm : 0 < m) :
    Gamma (MajorityBounds.majorityValue (n := 2 * m)) = 1 := by
  have hn : 1 ≤ 2 * m := by omega
  have hle : Gamma (MajorityBounds.majorityValue (n := 2 * m)) ≤ 1 := by
    have hc : LayerChange (MajorityBounds.majorityValue (n := 2 * m)) m := by
      rw [layerChange_majority_iff (by omega)]
      omega
    have hgl := gamma_le_of_layerChange
      (f := MajorityBounds.majorityValue (n := 2 * m)) (k := m) (by omega) hc
    have hdist : Nat.dist (2 * m + 1) (2 * m) = 1 := by
      rw [Nat.dist_eq_sub_of_le_right (by omega)]
      omega
    rw [hdist] at hgl
    exact hgl
  have hge : 1 ≤ Gamma (MajorityBounds.majorityValue (n := 2 * m)) := by
    obtain ⟨k, hk, hc, hd⟩ :=
      gamma_mem majorityValue_symmetric (majorityValue_nonconstant hn)
    have hcases := (layerChange_majority_iff (n := 2 * m) hk).mp hc
    have hdist : Nat.dist (2 * k + 1) (2 * m) = 1 := by
      rcases hcases with h | h
      · have hk' : k = m := by omega
        subst hk'
        rw [Nat.dist_eq_sub_of_le_right (by omega)]
        omega
      · omega
    rw [hd, hdist]
  exact le_antisymm hle hge

/-- Strict majority on `2 * m + 1` bits has jump parameter zero. -/
theorem gamma_majority_odd (m : ℕ) :
    Gamma (MajorityBounds.majorityValue (n := 2 * m + 1)) = 0 := by
  have hn : 1 ≤ 2 * m + 1 := by omega
  have hle : Gamma (MajorityBounds.majorityValue (n := 2 * m + 1)) ≤ 0 := by
    have hc : LayerChange (MajorityBounds.majorityValue (n := 2 * m + 1)) m := by
      rw [layerChange_majority_iff (by omega)]
      omega
    have hgl := gamma_le_of_layerChange
      (f := MajorityBounds.majorityValue (n := 2 * m + 1)) (k := m) (by omega) hc
    have hdist : Nat.dist (2 * m + 1) (2 * m + 1) = 0 := Nat.dist_self _
    rw [hdist] at hgl
    exact hgl
  omega

end Qatlib.Papers.PolyMethod01.SymDegree
