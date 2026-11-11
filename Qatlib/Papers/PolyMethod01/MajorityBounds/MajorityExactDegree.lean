/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact polynomial degree of strict majority

The predicate `majorityValue` is true when strictly more than half of the input bits are true.
The top Möbius coefficient is computed as an alternating binomial sum and shown to be nonzero
for positive input size, yielding exact degree equal to the number of variables. These results
accompany the polynomial-method analysis in [BealsEtAl2001].

## Main statements

* `mobiusCoef_majority_top_ne_zero`: For positive `n`, the top Möbius coefficient of strict
  majority is nonzero.
* `majority_exactDegree`: The exact real polynomial degree of strict majority on `n` bits is
  `n`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.MajorityBounds

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison
open scoped Classical BigOperators

/-- The Boolean strict-majority predicate, true when twice the number of true input bits exceeds
`n`. -/
def majorityValue {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide (n < 2 * (Finset.univ.filter (fun i => x i = true)).card)

/-- The Boolean characteristic function `chiSet T` is true at `i` exactly when `i` belongs to
`T`. -/
@[simp] theorem chiSet_apply {n : ℕ} (T : Finset (Fin n)) (i : Fin n) :
    chiSet T i = true ↔ i ∈ T := by
  simp [chiSet]

/-- Strict majority on the characteristic word of `T` is true exactly when `n < 2 * T.card`. -/
theorem majorityValue_chiSet {n : ℕ} (T : Finset (Fin n)) :
    majorityValue (chiSet T) = true ↔ n < 2 * T.card := by
  classical
  simp [majorityValue]

/-- The top Möbius coefficient of strict majority is the alternating binomial sum weighted by
its threshold indicator. -/
theorem mobiusCoef_majority_top (n : ℕ) :
    mobiusCoef (majorityValue (n := n)) (Finset.univ) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (n - k) * (if n < 2 * k then 1 else 0) * (n.choose k : ℝ) := by
  classical
  rw [mobiusCoef]
  have hterm : ∀ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ ((Finset.univ \ T).card) * bval (majorityValue (chiSet T)) =
        (-1 : ℝ) ^ (n - T.card) * (if n < 2 * T.card then 1 else 0) := by
    intro T _
    have hcard : (Finset.univ \ T).card = n - T.card := by
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
    rw [hcard]
    have hb : bval (majorityValue (chiSet T)) = if n < 2 * T.card then 1 else 0 := by
      by_cases h : n < 2 * T.card
      · have htrue : majorityValue (chiSet T) = true := (majorityValue_chiSet T).mpr h
        simp [bval, htrue, h]
      · have hfalse : majorityValue (chiSet T) = false := by
          cases hv : majorityValue (chiSet T) with
          | false => rfl
          | true => exact absurd ((majorityValue_chiSet T).mp hv) h
        simp [bval, hfalse, h]
    rw [hb]
  rw [Finset.sum_congr rfl hterm]
  have h := Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin n)))
    (f := fun k => (-1 : ℝ) ^ (n - k) * (if n < 2 * k then 1 else 0))
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]
  ring

/-- For `m ≤ n`, the alternating partial binomial sum through `m` equals `(-1) ^ m * choose (n -
1) m` over the reals. -/
theorem alternating_choose_partial (n : ℕ) :
    ∀ m ≤ n,
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ) ^ k * (n.choose k : ℝ))) =
        (-1 : ℝ) ^ m * ((n - 1).choose m : ℝ) := by
  intro m
  induction m with
  | zero =>
      intro _
      simp
  | succ m ih =>
      intro hm
      have hm' : m ≤ n := le_trans (Nat.le_succ m) hm
      rw [Finset.sum_range_succ, ih hm']
      have hn : 0 < n := by omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hpas : ((n' + 1).choose (m + 1) : ℝ) =
          ((n' + 1 - 1).choose (m + 1) : ℝ) + ((n' + 1 - 1).choose m : ℝ) := by
        rw [Nat.choose_succ_succ']
        push_cast
        ring
      rw [hpas]
      have hp : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by ring
      rw [hp]
      ring

/-- The strict-majority inequality `n < 2 * k` is equivalent to `n / 2 + 1 ≤ k` for natural
numbers. -/
theorem majority_threshold_iff (n k : ℕ) :
    n < 2 * k ↔ n / 2 + 1 ≤ k := by
  have h : n / 2 < k ↔ n < k * 2 := Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)
  constructor
  · intro hk
    have h1 : n / 2 < k := h.mpr (by omega)
    omega
  · intro hk
    have h1 : n / 2 < k := by omega
    have h2 : n < k * 2 := h.mp h1
    omega

/-- For positive `n`, reflecting the alternating binomial tail above the majority threshold
gives the stated alternating initial sum. -/
theorem majority_tail_reflect (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range (n + 1 - (n / 2 + 1)),
        (-1 : ℝ) ^ (n - (n / 2 + 1 + k)) * (n.choose (n / 2 + 1 + k) : ℝ)) =
      ∑ j ∈ Finset.range (n + 1 - (n / 2 + 1)), ((-1 : ℝ) ^ j * (n.choose j : ℝ)) := by
  classical
  set m0 : ℕ := n / 2 + 1 with hm0
  set N : ℕ := n + 1 - m0 with hN
  have hNm : m0 + N - 1 = n := by omega
  rw [← Finset.sum_range_reflect
    (fun j => (-1 : ℝ) ^ (n - (m0 + j)) * (n.choose (m0 + j) : ℝ)) N]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hklt : k < N := Finset.mem_range.mp hk
  have harg : n - (m0 + (N - 1 - k)) = k := by omega
  have hidx : m0 + (N - 1 - k) = n - k := by omega
  have hchoose : ((n.choose (m0 + (N - 1 - k)) : ℕ) : ℝ) = ((n.choose k : ℕ) : ℝ) := by
    rw [hidx]
    have hk' : k ≤ n := by omega
    rw [← Nat.choose_symm hk']
  rw [harg, hchoose]

/-- For positive `n`, the alternating binomial sum weighted by the strict-majority indicator is
nonzero. -/
theorem majority_top_alternating_ne_zero (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ (n - k) * (if n < 2 * k then 1 else 0) * (n.choose k : ℝ)) ≠ 0 := by
  classical
  set m0 : ℕ := n / 2 + 1 with hm0
  set g : ℕ → ℝ := fun k => (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) with hg
  have hcongr : (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ (n - k) * (if n < 2 * k then 1 else 0) * (n.choose k : ℝ)) =
      ∑ k ∈ Finset.range (n + 1), if m0 ≤ k then g k else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : n < 2 * k
    · have hk' : m0 ≤ k := (majority_threshold_iff n k).mp hk
      simp [g, hk, hk']
    · have hk' : ¬ m0 ≤ k := fun h => hk ((majority_threshold_iff n k).mpr h)
      simp [g, hk, hk']
  rw [hcongr]
  have hle : m0 ≤ n + 1 := by omega
  have hsplit : (∑ k ∈ Finset.range (n + 1), if m0 ≤ k then g k else 0) =
      (∑ k ∈ Finset.range m0, if m0 ≤ k then g k else 0) +
        ∑ k ∈ Finset.range (n + 1 - m0), (if m0 ≤ m0 + k then g (m0 + k) else 0) := by
    have hadd : m0 + (n + 1 - m0) = n + 1 := by omega
    calc (∑ k ∈ Finset.range (n + 1), if m0 ≤ k then g k else 0)
        = ∑ k ∈ Finset.range (m0 + (n + 1 - m0)), (if m0 ≤ k then g k else 0) := by
          rw [hadd]
      _ = _ := Finset.sum_range_add (fun k => if m0 ≤ k then g k else 0) m0 (n + 1 - m0)
  rw [hsplit]
  have hleft : (∑ k ∈ Finset.range m0, if m0 ≤ k then g k else 0) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hlt : k < m0 := Finset.mem_range.mp hk
    simp [Nat.not_le.mpr hlt]
  rw [hleft, zero_add]
  have hshift : (∑ k ∈ Finset.range (n + 1 - m0),
      (if m0 ≤ m0 + k then g (m0 + k) else 0)) =
      ∑ k ∈ Finset.range (n + 1 - m0),
        (-1 : ℝ) ^ (n - (n / 2 + 1 + k)) * (n.choose (n / 2 + 1 + k) : ℝ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos (Nat.le_add_right m0 k)]
  rw [hshift]
  rw [majority_tail_reflect n hn]
  have hval := alternating_choose_partial n (n + 1 - (n / 2 + 1) - 1) (by omega)
  have hlen : n + 1 - (n / 2 + 1) - 1 + 1 = n + 1 - (n / 2 + 1) := by omega
  rw [← hlen, hval]
  have hpos : 0 < (n - 1).choose (n + 1 - (n / 2 + 1) - 1) := by
    apply Nat.choose_pos
    omega
  have hcast : (0 : ℝ) < (((n - 1).choose (n + 1 - (n / 2 + 1) - 1) : ℕ) : ℝ) := by
    exact_mod_cast hpos
  have hsign : (-1 : ℝ) ^ (n + 1 - (n / 2 + 1) - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero hsign (ne_of_gt hcast)

/-- For positive `n`, the top Möbius coefficient of strict majority is nonzero. -/
theorem mobiusCoef_majority_top_ne_zero (n : ℕ) (hn : 0 < n) :
    mobiusCoef (majorityValue (n := n)) (Finset.univ) ≠ 0 := by
  rw [mobiusCoef_majority_top]
  exact majority_top_alternating_ne_zero n hn

/-- The Möbius degree of strict majority on `n` bits is `n`. -/
theorem majority_mobiusDegree (n : ℕ) :
    mobiusDegree (majorityValue (n := n)) = n := by
  classical
  refine le_antisymm ?_ ?_
  · unfold mobiusDegree
    refine Finset.sup_le fun S hS => ?_
    obtain ⟨hS', _⟩ := Finset.mem_filter.mp hS
    have hS'' : S ⊆ (Finset.univ : Finset (Fin n)) := Finset.mem_powerset.mp hS'
    simpa using! Finset.card_le_card hS''
  · cases n with
    | zero => simp
    | succ m =>
        have hpos : (Finset.univ : Finset (Fin (m + 1))).card ≤
            mobiusDegree (majorityValue (n := m + 1)) :=
          card_le_mobiusDegree (mobiusCoef_majority_top_ne_zero (m + 1) (Nat.succ_pos m))
        simpa using! hpos

/-- The exact real polynomial degree of strict majority on `n` bits is `n`. See [Beals et al.,
2001][BealsEtAl2001]. -/
theorem majority_exactDegree (n : ℕ) :
    exactDegree (majorityValue (n := n)) = n := by
  rw [← mobiusDegree_eq_exactDegree]
  exact majority_mobiusDegree n

/-- Every real multivariate polynomial representing strict majority on `n` bits has total degree
at least `n`. -/
theorem majority_totalDegree_ge (n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ x : Fin n → Bool, boolEval p x = if majorityValue x then (1 : ℝ) else 0) :
    n ≤ p.totalDegree := by
  have hmem : p.totalDegree ∈ (fun q : MvPolynomial (Fin n) ℝ => q.totalDegree) ''
      {q | ∀ x : Fin n → Bool, boolEval q x = if majorityValue x then (1 : ℝ) else 0} :=
    ⟨p, hp, rfl⟩
  have hle : exactDegree (majorityValue (n := n)) ≤ p.totalDegree := Nat.sInf_le hmem
  rw [majority_exactDegree] at hle
  exact hle

end Qatlib.Papers.PolyMethod01.MajorityBounds
