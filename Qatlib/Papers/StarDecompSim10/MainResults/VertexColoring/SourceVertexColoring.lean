/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bitwise
import Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition.SourceForestDecomposition

set_option backward.isDefEq.respectTransparency false

/-!
# Forest 6-Coloring via Deterministic Coin Tossing

This module formalizes Lemma 2 of [Childs and Kothari, 2011][ChildsKothari2011] (§4, pp. 7–8):
given a forest of arborescences represented by a parent map with `parent v < v` (the output
of Lemma 1), deterministic coin tossing refines the trivial `N`-coloring in `log* N + 1`
rounds to a proper 6-coloring whose value at each vertex `v` depends only on the first
`log* N + 1` ancestors of `v` (`O(log* N)` parent-oracle queries).

## Main statements

* `refineVal_proper`: one round of coin-tossing refinement preserves properness.
* `iterate_nextBits_logStar_le_three`: iterating `L ↦ ⌈log₂ L⌉ + 1` for `log* N` rounds
  reduces `⌊log₂ N⌋ + 1` bits to at most 3 bits.
* `colorAt_logStar_succ_lt_six`: after `log* N + 1` rounds, fewer than 6 colors are used.
* `vertex_coloring_six`: bundled Lemma 2 statement (properness, 6-color bound, and
  `log* N + 1` ancestor-chain locality).

## References

* [Childs and Kothari, 2011][ChildsKothari2011]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.StarDecompSim10.MainResults.VertexColoring

open Finset
open Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition

variable {N : ℕ}

/-! ## `log*` -/

/-- The paper's iterated logarithm (footnote 4, p. 4): `log* N = 0` for
`N ≤ 1`, and `log* N = 1 + log* (⌊log₂ N⌋)` otherwise. -/
def logStar : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + logStar (Nat.log2 (n + 2))
termination_by n => n
decreasing_by
  simp_wf
  by_contra hnot
  have hge : n + 2 ≤ Nat.log2 (n + 2) := by omega
  have hp : 2 ^ (n + 2) ≤ n + 2 :=
    (Nat.le_log2 (by omega : n + 2 ≠ 0)).mp hge
  have := Nat.lt_two_pow_self (n := n + 2)
  omega

/-! ## The most significant differing bit -/

/-- The index of the most significant set bit of a positive number, and `0`
at zero.  Used as the paper's "first bit at which the two colours differ". -/
def msb (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else Classical.choose (Nat.exists_most_significant_bit h)

/-- The chosen bit is set. -/
theorem msb_testBit (n : ℕ) (h : n ≠ 0) : n.testBit (msb n) = true := by
  unfold msb
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec (Nat.exists_most_significant_bit h)).1

/-- All bits above the most significant one are zero. -/
theorem msb_above_false (n : ℕ) (h : n ≠ 0) {j : ℕ} (hj : msb n < j) :
    n.testBit j = false := by
  unfold msb at hj
  simp only [h, ↓reduceDIte] at hj
  exact (Classical.choose_spec (Nat.exists_most_significant_bit h)).2 j hj

/-- The index of the most significant differing bit of `a` and `b`. -/
def topDiff (a b : ℕ) : ℕ := msb (a ^^^ b)

/-- Distinct numbers differ at their most significant differing bit. -/
theorem topDiff_testBit_ne {a b : ℕ} (h : a ≠ b) :
    a.testBit (topDiff a b) ≠ b.testBit (topDiff a b) := by
  have hxor : a ^^^ b ≠ 0 := Nat.xor_ne_zero_iff.mpr h
  have hspec : (a ^^^ b).testBit (topDiff a b) = true := msb_testBit _ hxor
  rw [Nat.testBit_xor] at hspec
  intro heq
  rw [heq] at hspec
  simp at hspec

/-- The bit value at position `k`, as `0` or `1`. -/
def bitVal (a k : ℕ) : ℕ := if a.testBit k then 1 else 0

/-- The bit Val lt two property in the paper model. -/
theorem bitVal_lt_two (a k : ℕ) : bitVal a k < 2 := by
  unfold bitVal
  split <;> norm_num

/-- The bit Val ne of test Bit ne property in the paper model. -/
theorem bitVal_ne_of_testBit_ne {a b k : ℕ} (h : a.testBit k ≠ b.testBit k) :
    bitVal a k ≠ bitVal b k := by
  unfold bitVal
  cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp_all

/-! ## One refinement round -/

/-- One round of the coin-tossing refinement, with the paper's root rule
`k = 0`; the second coordinate of a root is the bit `b` at position `0`, so a
root's colour never collides with a child whose first differing bit is `0`
(the bit of the child at `0` is opposite to the root's). -/
def refineVal (parent : Fin N → Option (Fin N)) (κ : Fin N → ℕ) (v : Fin N) : ℕ :=
  match parent v with
  | none => bitVal (κ v) 0
  | some p =>
      let k := topDiff (κ v) (κ p)
      2 * k + bitVal (κ v) k

/-- **Properness of one refinement round** (proof of Lemma 2, pp. 7--8): if
`κ` is a proper colouring of the forest, then `refineVal` is proper. -/
theorem refineVal_proper (parent : Fin N → Option (Fin N)) (κ : Fin N → ℕ)
    (hproper : ∀ v p, parent v = some p → κ v ≠ κ p) :
    ∀ v p, parent v = some p → refineVal parent κ v ≠ refineVal parent κ p := by
  intro v p hvp
  have hv_ne : κ v ≠ κ p := hproper v p hvp
  have hk : (κ v).testBit (topDiff (κ v) (κ p)) ≠ (κ p).testBit (topDiff (κ v) (κ p)) :=
    topDiff_testBit_ne hv_ne
  have hvr : refineVal parent κ v =
      2 * topDiff (κ v) (κ p) + bitVal (κ v) (topDiff (κ v) (κ p)) := by
    simp [refineVal, hvp]
  cases hp : parent p with
  | none =>
      have hpr : refineVal parent κ p = bitVal (κ p) 0 := by simp [refineVal, hp]
      rw [hvr, hpr]
      intro heq
      have hb1 : bitVal (κ v) (topDiff (κ v) (κ p)) < 2 := bitVal_lt_two _ _
      have hb0 : bitVal (κ p) 0 < 2 := bitVal_lt_two _ _
      have hk0 : topDiff (κ v) (κ p) = 0 := by omega
      have hbb : bitVal (κ v) (topDiff (κ v) (κ p)) = bitVal (κ p) 0 := by omega
      have hbit : bitVal (κ v) 0 = bitVal (κ p) 0 := by rwa [hk0] at hbb
      have hk0' : (κ v).testBit 0 ≠ (κ p).testBit 0 := by rwa [hk0] at hk
      exact bitVal_ne_of_testBit_ne hk0' hbit
  | some q =>
      have hp_ne : κ p ≠ κ q := hproper p q hp
      have hpr : refineVal parent κ p =
          2 * topDiff (κ p) (κ q) + bitVal (κ p) (topDiff (κ p) (κ q)) := by
        simp [refineVal, hp]
      rw [hvr, hpr]
      intro heq
      have hb1 : bitVal (κ v) (topDiff (κ v) (κ p)) < 2 := bitVal_lt_two _ _
      have hb2 : bitVal (κ p) (topDiff (κ p) (κ q)) < 2 := bitVal_lt_two _ _
      have hkk : topDiff (κ v) (κ p) = topDiff (κ p) (κ q) := by omega
      have hbb : bitVal (κ v) (topDiff (κ v) (κ p)) =
          bitVal (κ p) (topDiff (κ p) (κ q)) := by omega
      have hbit : bitVal (κ v) (topDiff (κ v) (κ p)) =
          bitVal (κ p) (topDiff (κ v) (κ p)) := by rw [hbb, hkk]
      exact bitVal_ne_of_testBit_ne hk hbit

/-! ## Bit width of a refinement -/

/-- `BelowBits L κ`: every colour is `< 2^L` (so `L` bits suffice). -/
def BelowBits (L : ℕ) (κ : Fin N → ℕ) : Prop := ∀ v, κ v < 2 ^ L

/-- The bit width after one round, when `L` bits were used: `⌈log L⌉ + 1`,
written as `log₂ (2L-1) + 1` (the largest new colour is `2(L-1)+1 = 2L-1`). -/
def nextBits (L : ℕ) : ℕ := Nat.log2 (2 * L - 1) + 1

/-- Width is always at least one bit. -/
theorem nextBits_pos (L : ℕ) : 0 < nextBits L := by
  unfold nextBits; omega

/-- **Range bound of one refinement round**: `L` bits map to `nextBits L`
bits. -/
theorem refineVal_lt_nextBits (parent : Fin N → Option (Fin N)) {L : ℕ}
    {κ : Fin N → ℕ} (hκ : BelowBits L κ) (v : Fin N) :
    refineVal parent κ v < 2 ^ nextBits L := by
  unfold refineVal
  cases h : parent v with
  | none =>
      change bitVal (κ v) 0 < 2 ^ nextBits L
      have hb : bitVal (κ v) 0 < 2 := bitVal_lt_two _ _
      have hpow : 2 ≤ 2 ^ nextBits L := by
        have hpos := nextBits_pos L
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ nextBits L := Nat.pow_le_pow_right (by norm_num) hpos
      omega
  | some p =>
      change 2 * topDiff (κ v) (κ p) + bitVal (κ v) (topDiff (κ v) (κ p)) < 2 ^ nextBits L
      set k := topDiff (κ v) (κ p) with hkdef
      by_cases hx0 : κ v ^^^ κ p = 0
      · have hk0 : k = 0 := by simp [hkdef, topDiff, msb, hx0]
        have hb0 : bitVal (κ v) 0 < 2 := bitVal_lt_two _ _
        have hpow : 2 ≤ 2 ^ nextBits L := by
          have hpos := nextBits_pos L
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ nextBits L := Nat.pow_le_pow_right (by norm_num) hpos
        rw [hk0]
        omega
      · have hvx : κ v < 2 ^ L := hκ v
        have hpx : κ p < 2 ^ L := hκ p
        have hxorlt : (κ v ^^^ κ p) < 2 ^ L := Nat.xor_lt_two_pow hvx hpx
        have hbound : 2 ^ k ≤ κ v ^^^ κ p := by
          apply Nat.two_pow_le_of_mem_bitIndices
          apply Nat.mem_bitIndices.mpr
          change (κ v ^^^ κ p).testBit (msb (κ v ^^^ κ p)) = true
          exact msb_testBit _ hx0
        have hkL : k < L := by
          by_contra hnot
          have hge : L ≤ k := le_of_not_gt hnot
          have hmono : 2 ^ L ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
          omega
        have hk_le : k ≤ L - 1 := by omega
        have hb : bitVal (κ v) k < 2 := bitVal_lt_two _ _
        have hval : 2 * k + bitVal (κ v) k ≤ 2 * L - 1 := by omega
        have hxpos : 2 * L - 1 ≠ 0 := by omega
        have hlt : 2 * L - 1 < 2 ^ nextBits L := by
          unfold nextBits
          exact ((Nat.log2_eq_iff hxpos).mp rfl).2
        omega

/-! ## Iterating the refinement -/

/-- The colour after `j` rounds, starting from the label colouring. -/
def colorAt (parent : Fin N → Option (Fin N)) : ℕ → Fin N → ℕ
  | 0 => fun v => v.val
  | j + 1 => fun v => refineVal parent (colorAt parent j) v

/-- Every round preserves properness. -/
theorem colorAt_proper {parent : Fin N → Option (Fin N)}
    (hpar : ∀ v w, parent v = some w → w < v) :
    ∀ j, ∀ v w, parent v = some w → colorAt parent j v ≠ colorAt parent j w := by
  intro j
  induction j with
  | zero =>
      intro v w h
      have : w < v := hpar v w h
      simp only [colorAt]
      omega
  | succ j ih =>
      exact refineVal_proper parent (colorAt parent j) ih

/-- Every round obeys the bit-width recurrence. -/
theorem colorAt_belowBits (parent : Fin N → Option (Fin N)) :
    ∀ j, BelowBits (Nat.iterate nextBits j (Nat.log2 N + 1)) (colorAt parent j) := by
  intro j
  induction j with
  | zero =>
      intro v
      simp only [colorAt]
      show v.val < 2 ^ Nat.iterate nextBits 0 (Nat.log2 N + 1)
      rw [Function.iterate_zero]
      change v.val < 2 ^ (Nat.log2 N + 1)
      have h1 : v.val < N := v.isLt
      have h2 : N < 2 ^ (Nat.log2 N + 1) := by
        by_cases hN : N = 0
        · subst hN; simp
        · exact ((Nat.log2_eq_iff hN).mp rfl).2
      omega
  | succ j ih =>
      intro v
      have hstep : Nat.iterate nextBits (j + 1) (Nat.log2 N + 1) =
          nextBits (Nat.iterate nextBits j (Nat.log2 N + 1)) := by
        rw [Function.iterate_succ_apply']
      rw [hstep]
      exact refineVal_lt_nextBits parent ih v

/-- If three bits suffice for `κ`, one refinement round gives fewer than six
colours: `k ∈ {0,1,2}` and the bit is `0` or `1`, so `2k+b ≤ 5`. -/
theorem refineVal_lt_six (parent : Fin N → Option (Fin N)) {κ : Fin N → ℕ}
    (hκ : BelowBits 3 κ) (v : Fin N) : refineVal parent κ v < 6 := by
  unfold refineVal
  cases h : parent v with
  | none =>
      change bitVal (κ v) 0 < 6
      have := bitVal_lt_two (κ v) 0
      omega
  | some p =>
      change 2 * topDiff (κ v) (κ p) + bitVal (κ v) (topDiff (κ v) (κ p)) < 6
      by_cases hx0 : κ v ^^^ κ p = 0
      · have hk0 : topDiff (κ v) (κ p) = 0 := by simp [topDiff, msb, hx0]
        have := bitVal_lt_two (κ v) 0
        rw [hk0]
        omega
      · have hvx : κ v < 2 ^ 3 := hκ v
        have hpx : κ p < 2 ^ 3 := hκ p
        have hxorlt : (κ v ^^^ κ p) < 2 ^ 3 := Nat.xor_lt_two_pow hvx hpx
        have hbound : 2 ^ topDiff (κ v) (κ p) ≤ κ v ^^^ κ p := by
          apply Nat.two_pow_le_of_mem_bitIndices
          apply Nat.mem_bitIndices.mpr
          change (κ v ^^^ κ p).testBit (msb (κ v ^^^ κ p)) = true
          exact msb_testBit _ hx0
        have hkL : topDiff (κ v) (κ p) < 3 := by
          by_contra hnot
          have hge : 3 ≤ topDiff (κ v) (κ p) := le_of_not_gt hnot
          have hmono : 2 ^ 3 ≤ 2 ^ topDiff (κ v) (κ p) :=
            Nat.pow_le_pow_right (by norm_num) hge
          omega
        have := bitVal_lt_two (κ v) (topDiff (κ v) (κ p))
        omega

/-- One step of `nextBits` maps any width `L ≤ 2^m` to at most `m + 1`. -/
private theorem nextBits_le_of_le_two_pow {L m : ℕ} (h : L ≤ 2 ^ m) :
    nextBits L ≤ m + 1 := by
  unfold nextBits
  by_cases hL : L = 0
  · subst hL; simp
  · by_contra hnot
    have hge : m + 1 ≤ Nat.log2 (2 * L - 1) := by omega
    have hp : 2 ^ (m + 1) ≤ 2 * L - 1 :=
      (Nat.le_log2 (by omega : 2 * L - 1 ≠ 0)).mp hge
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    omega

/-- Auxiliary exponential tower inverse to `nextBits`, starting at `3`. -/
private def preTower : ℕ → ℕ
  | 0 => 3
  | r + 1 => 2 ^ (preTower r - 1)

private theorem three_le_preTower : ∀ r : ℕ, 3 ≤ preTower r
  | 0 => le_rfl
  | r + 1 => by
      have ih := three_le_preTower r
      have hpow : 2 ^ 2 ≤ 2 ^ (preTower r - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      change 3 ≤ 2 ^ (preTower r - 1)
      omega

private theorem iterate_nextBits_le_three_of_le_preTower :
    ∀ (r L : ℕ), L ≤ preTower r → Nat.iterate nextBits r L ≤ 3
  | 0, L, hL => hL
  | r + 1, L, hL => by
      rw [Function.iterate_succ_apply]
      apply iterate_nextBits_le_three_of_le_preTower r
      have hstep : nextBits L ≤ (preTower r - 1) + 1 :=
        nextBits_le_of_le_two_pow hL
      have h3 := three_le_preTower r
      omega

private theorem log2_add_three_le_preTower :
    ∀ N : ℕ, 2 ≤ N → Nat.log2 N + 3 ≤ preTower (logStar N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN2
      by_cases hN4 : N < 4
      · rcases (by omega : N = 2 ∨ N = 3) with rfl | rfl
        · have hlog : Nat.log2 2 = 1 := by decide
          have hls : logStar 2 = 1 := by rw [logStar, hlog, logStar]
          rw [hlog, hls]
          decide
        · have hlog : Nat.log2 3 = 1 := by decide
          have hls : logStar 3 = 1 := by rw [logStar, hlog, logStar]
          rw [hlog, hls]
          decide
      · have hN4' : 4 ≤ N := le_of_not_gt hN4
        set K := Nat.log2 N with hKdef
        have hK2 : 2 ≤ K := by
          rw [hKdef, Nat.le_log2 (by omega : N ≠ 0)]
          omega
        have hKN : K < N := by
          by_contra hnot
          have hge : N ≤ Nat.log2 N := by omega
          have hp : 2 ^ N ≤ N := (Nat.le_log2 (by omega : N ≠ 0)).mp hge
          have hlt := Nat.lt_two_pow_self (n := N)
          omega
        have hls : logStar N = logStar K + 1 := by
          obtain ⟨m, hm⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
          have hls1 : logStar N = 1 + logStar (Nat.log2 N) := by
            rw [hm, logStar]
          rw [hls1, ← hKdef]
          omega
        have ihK := ih K hKN hK2
        have hpow_mono : 2 ^ (Nat.log2 K + 2) ≤ preTower (logStar N) := by
          rw [hls]
          change 2 ^ (Nat.log2 K + 2) ≤ 2 ^ (preTower (logStar K) - 1)
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hK_lt : K < 2 ^ (Nat.log2 K + 1) :=
          ((Nat.log2_eq_iff (by omega : K ≠ 0)).mp rfl).2
        have hpow_succ : 2 ^ (Nat.log2 K + 2) = 2 ^ (Nat.log2 K + 1) * 2 :=
          pow_succ 2 (Nat.log2 K + 1)
        omega

/-- **Bit-width arithmetic of Lemma 2** ([Childs and Kothari, 2011][ChildsKothari2011], §4, p. 7):
starting from `⌊log₂ N⌋ + 1` bits, the recurrence `L ↦ ⌈log₂ L⌉ + 1` reaches at most three
bits after `log* N` rounds. -/
theorem iterate_nextBits_logStar_le_three (N : ℕ) :
    Nat.iterate nextBits (logStar N) (Nat.log2 N + 1) ≤ 3 := by
  apply iterate_nextBits_le_three_of_le_preTower
  by_cases hN : N < 2
  · rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
    · rw [logStar]; decide
    · rw [logStar]; decide
  · have h := log2_add_three_le_preTower N (by omega)
    omega

/-- After `log* N` rounds at most three bits suffice. -/
theorem colorAt_logStar_belowBits (parent : Fin N → Option (Fin N)) :
    BelowBits 3 (colorAt parent (logStar N)) := by
  have h := colorAt_belowBits parent (logStar N)
  intro v
  have hv := h v
  have hle := iterate_nextBits_logStar_le_three N
  have : (2 : ℕ) ^ Nat.iterate nextBits (logStar N) (Nat.log2 N + 1) ≤ 2 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) hle
  omega

/-- **Six-colour bound** (p. 7): after `log* N + 1` rounds fewer than six
colours are used. -/
theorem colorAt_logStar_succ_lt_six (parent : Fin N → Option (Fin N)) (v : Fin N) :
    colorAt parent (logStar N + 1) v < 6 := by
  have h3 : BelowBits 3 (colorAt parent (logStar N)) := colorAt_logStar_belowBits parent
  have hstep : colorAt parent (logStar N + 1) v =
      refineVal parent (colorAt parent (logStar N)) v := rfl
  rw [hstep]
  exact refineVal_lt_six parent h3 v

/-! ## Query locality: only the ancestor chain is read -/

/-- The vertices whose parent entries are read during `j` rounds starting at
`v`: the first `j` ancestors of `v` (fewer at a root). -/
def reach (parent : Fin N → Option (Fin N)) : ℕ → Fin N → Finset (Fin N)
  | 0 => fun v => {v}
  | j + 1 => fun v =>
      insert v (match parent v with
        | none => ∅
        | some p => reach parent j p)

/-- The reachable chain has at most `j + 1` vertices, so `j` parent queries
suffice. -/
theorem reach_card_le (parent : Fin N → Option (Fin N)) (j : ℕ) (v : Fin N) :
    (reach parent j v).card ≤ j + 1 := by
  induction j generalizing v with
  | zero => simp [reach]
  | succ j ih =>
      cases h : parent v with
      | none =>
          simp [reach, h]
      | some p =>
          simp only [reach, h]
          calc (insert v (reach parent j p)).card ≤ (reach parent j p).card + 1 :=
                Finset.card_insert_le _ _
            _ ≤ (j + 1) + 1 := by
                have := ih p
                omega

/-- `reach` is monotone in the number of rounds. -/
theorem reach_mono (parent : Fin N → Option (Fin N)) :
    ∀ (v : Fin N) {i j : ℕ}, i ≤ j → reach parent i v ⊆ reach parent j v := by
  intro v i j hij
  induction j generalizing i v with
  | zero =>
      have h0 : i = 0 := by omega
      subst h0
      exact Finset.Subset.refl _
  | succ j ih =>
      by_cases hji : i = j + 1
      · subst hji
        exact Finset.Subset.refl _
      · have hij' : i ≤ j := by omega
        cases i with
        | zero => simp [reach]
        | succ i =>
            cases h : parent v with
            | none =>
                have hnone : reach parent (j + 1) v = {v} := by simp [reach, h]
                have hnone' : reach parent (i + 1) v = {v} := by simp [reach, h]
                rw [hnone', hnone]
            | some p =>
                simp only [reach, h]
                exact Finset.insert_subset_insert v (ih (v := p) (i := i) (by omega))

/-- **Locality of the colour**: the colour at `v` after `j` rounds is
determined by the parent entries on `reach parent j v`, i.e. by `j` oracle
queries to the parent oracle. -/
theorem colorAt_congr {parent parent' : Fin N → Option (Fin N)} (j : ℕ) (v : Fin N)
    (h : ∀ u ∈ reach parent j v, parent' u = parent u) :
    colorAt parent' j v = colorAt parent j v := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
      have hv_mem : v ∈ reach parent (j + 1) v := by simp [reach]
      have hv : parent' v = parent v := h v hv_mem
      have hstep' : colorAt parent' (j + 1) v = refineVal parent' (colorAt parent' j) v := rfl
      have hstep : colorAt parent (j + 1) v = refineVal parent (colorAt parent j) v := rfl
      rw [hstep', hstep]
      unfold refineVal
      rw [hv]
      cases hp : parent v with
      | none =>
          -- the whole chain collapses to `v`
          have hvsub : reach parent j v ⊆ reach parent (j + 1) v :=
            reach_mono parent v (by omega)
          have h' : ∀ u ∈ reach parent j v, parent' u = parent u :=
            fun u hu => h u (hvsub hu)
          change bitVal (colorAt parent' j v) 0 = bitVal (colorAt parent j v) 0
          rw [ih v h']
      | some p =>
          have hsubj : reach parent j v ⊆ reach parent (j + 1) v :=
            reach_mono parent v (by omega)
          have hsubp : reach parent j p ⊆ reach parent (j + 1) v := by
            intro u hu
            simp only [reach, hp]
            exact Finset.mem_insert_of_mem hu
          have h'v : ∀ u ∈ reach parent j v, parent' u = parent u :=
            fun u hu => h u (hsubj hu)
          have h'p : ∀ u ∈ reach parent j p, parent' u = parent u :=
            fun u hu => h u (hsubp hu)
          change 2 * topDiff (colorAt parent' j v) (colorAt parent' j p) +
              bitVal (colorAt parent' j v) (topDiff (colorAt parent' j v) (colorAt parent' j p)) =
            2 * topDiff (colorAt parent j v) (colorAt parent j p) +
              bitVal (colorAt parent j v) (topDiff (colorAt parent j v) (colorAt parent j p))
          rw [ih v h'v, ih p h'p]

/-! ## Lemma 2, bundled -/

/-- **Lemma 2 (Vertex coloring a forest)**, arXiv:1003.3683v2 §4 p.7--8.
If `parent` is a forest of arborescences with the one-query parent oracle
(`parent v < v`, as produced by Lemma 1), then there is a proper 6-colouring
of the forest whose colour at `v` is computed by `log* N + 1` parent queries:
the colour is `colorAt parent (log* N + 1) v`, and it depends only on the
`log* N + 1` ancestors `reach parent (log* N + 1) v`. -/
theorem vertex_coloring_six {parent : Fin N → Option (Fin N)}
    (hpar : ∀ v w, parent v = some w → w < v) :
    ∃ χ : Fin N → Fin 6,
      (∀ v w, parent v = some w → χ v ≠ χ w) ∧
      (∀ v, (χ v).val = colorAt parent (logStar N + 1) v) ∧
      (∀ v, (reach parent (logStar N + 1) v).card ≤ logStar N + 2) ∧
      (∀ (parent' : Fin N → Option (Fin N)) (v : Fin N),
        (∀ u ∈ reach parent (logStar N + 1) v, parent' u = parent u) →
          colorAt parent' (logStar N + 1) v = colorAt parent (logStar N + 1) v) := by
  refine ⟨fun v => ⟨colorAt parent (logStar N + 1) v, colorAt_logStar_succ_lt_six parent v⟩,
    ?_, ?_, ?_⟩
  · intro v w hvw heq
    exact colorAt_proper hpar (logStar N + 1) v w hvw (congrArg Fin.val heq)
  · intro v; rfl
  · refine ⟨fun v => reach_card_le parent (logStar N + 1) v, ?_⟩
    intro parent' v h
    exact colorAt_congr (logStar N + 1) v h

end Qatlib.Papers.StarDecompSim10.MainResults.VertexColoring
