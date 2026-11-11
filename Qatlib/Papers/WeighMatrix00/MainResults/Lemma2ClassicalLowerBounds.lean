/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Papers.WeighMatrix00.MainResults.WeighingMatrix

/-!
# Classical query lower bounds for weighing matrices

This module defines ternary decision trees in `QueryTree` and counts the inputs on which they
recover a row of a weighing matrix. Bounds using tree depth, binary branches, and column
sparsity yield the three inequalities in `source_lemma2_classicalLowerBounds` and their Hadamard
specialization.

This development forms part of the formalization of [VanDam2002].

## Main statements

* `QueryTree`: A ternary query tree with query indices and output labels in `Fin n`.
* `source_lemma2_classicalLowerBounds`: For `0 < ε < 1` and `0 < k ≤ n`, a tree recovering at
  least a `1 - ε` fraction of rows satisfies the ternary logarithmic, linear-in-weight, and
  binary logarithmic lower bounds on its depth.
* `source_lemma2_hadamardCase`: In the Hadamard case `k = n > 0` with `0 < ε < 1`, recovering at
  least a `1 - ε` fraction of rows requires depth at least `log n / log 2 + log (1 - ε) / log
  2`.

## References

* [van Dam, 2002][VanDam2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

/-- A ternary query tree with query indices and output labels in `Fin n`. -/
inductive QueryTree (n : ℕ) where

  | leaf (s : Fin n) : QueryTree n

  | node (i : Fin n) (minus zero plus : QueryTree n) : QueryTree n

namespace QueryTree

variable {n : ℕ}

/-- The maximum number of queries along a path from the root to a leaf. -/
def depth : QueryTree n → ℕ
  | leaf _ => 0
  | node _ a b c => 1 + max a.depth (max b.depth c.depth)

/-- The number of leaves of a ternary query tree. -/
def leaves : QueryTree n → ℕ
  | leaf _ => 1
  | node _ a b c => a.leaves + b.leaves + c.leaves

/-- Encode an oracle value of -1, 0, or any other integer by branch 0, 1, or 2, respectively. -/
def branch (f : Fin n → ℤ) (i : Fin n) : Fin 3 :=
  if f i = -1 then 0 else if f i = 0 then 1 else 2

/-- The middle branch is selected exactly when the queried oracle value is zero. -/
theorem branch_eq_one_iff (f : Fin n → ℤ) (i : Fin n) :
    branch f i = 1 ↔ f i = 0 := by
  unfold branch
  by_cases h1 : f i = -1
  · rw [if_pos h1]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · by_cases h2 : f i = 0
    · rw [if_neg h1, if_pos h2]
      exact ⟨fun _ => h2, fun _ => rfl⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩

/-- Evaluate a query tree by following the branches selected by the oracle function. -/
def eval : QueryTree n → (Fin n → ℤ) → Fin n
  | leaf s, _ => s
  | node i a b c, f =>
      if branch f i = 0 then a.eval f else if branch f i = 1 then b.eval f else c.eval f

/-- A ternary query tree has at most `3 ^ t.depth` leaves. -/
theorem leaves_le_three_pow (t : QueryTree n) : t.leaves ≤ 3 ^ t.depth := by
  induction t with
  | leaf _ => simp [leaves, depth]
  | node i a b c iha ihb ihc =>
    simp only [leaves, depth]
    set D := max a.depth (max b.depth c.depth) with hD
    have hda : a.depth ≤ D := by rw [hD]; exact le_max_left _ _
    have hdb : b.depth ≤ D := by
      rw [hD]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hdc : c.depth ≤ D := by
      rw [hD]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have ha3 : 3 ^ a.depth ≤ 3 ^ D := Nat.pow_le_pow_right (by norm_num) hda
    have hb3 : 3 ^ b.depth ≤ 3 ^ D := Nat.pow_le_pow_right (by norm_num) hdb
    have hc3 : 3 ^ c.depth ≤ 3 ^ D := Nat.pow_le_pow_right (by norm_num) hdc
    have hsum : a.leaves + b.leaves + c.leaves ≤ 3 ^ D + 3 ^ D + 3 ^ D := by omega
    have hpow : 3 ^ D + 3 ^ D + 3 ^ D = 3 ^ (1 + D) := by
      rw [show 1 + D = D + 1 by omega, pow_succ]
      ring
    rw [hpow] at hsum
    exact hsum

/-- The number of labels in `S` correctly recovered from the corresponding oracle functions is
at most the number of leaves. -/
theorem correct_card_le_leaves (t : QueryTree n) (g : Fin n → Fin n → ℤ)
    (S : Finset (Fin n)) :
    (S.filter (fun s => t.eval (g s) = s)).card ≤ t.leaves := by
  induction t generalizing S with
  | leaf s0 =>
    have h1 : (S.filter (fun s => (QueryTree.leaf s0).eval (g s) = s)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter, eval] at ha hb
      exact ha.2.symm.trans hb.2
    simpa [leaves] using h1
  | node i a b c iha ihb ihc =>
    set W := S.filter (fun s => (QueryTree.node i a b c).eval (g s) = s) with hW
    set Z := S.filter (fun s => branch (g s) i = 1 ∧ b.eval (g s) = s) with hZ
    set Na := S.filter (fun s => branch (g s) i = 0 ∧ a.eval (g s) = s) with hNa
    set Nc := S.filter (fun s => branch (g s) i = 2 ∧ c.eval (g s) = s) with hNc
    have hsub : W ⊆ Z ∪ (Na ∪ Nc) := by
      intro s hs
      simp only [hW, Finset.mem_filter] at hs
      obtain ⟨hsS, hcorr⟩ := hs
      by_cases h0 : branch (g s) i = 0
      · simp only [Finset.mem_union, Finset.mem_filter, hZ, hNa, hNc]
        right; left
        exact ⟨hsS, h0, by simpa [eval, h0] using hcorr⟩
      · by_cases h1 : branch (g s) i = 1
        · simp only [Finset.mem_union, Finset.mem_filter, hZ, hNa, hNc]
          left
          exact ⟨hsS, h1, by simpa [eval, h0, h1] using hcorr⟩
        · have h2 : branch (g s) i = 2 := by
            apply Fin.ext
            have hv0 : (branch (g s) i).val ≠ 0 := fun hv => h0 (Fin.ext hv)
            have hv1 : (branch (g s) i).val ≠ 1 := fun hv => h1 (Fin.ext hv)
            have hv2 : (branch (g s) i).val < 3 := Fin.is_lt _
            omega
          simp only [Finset.mem_union, Finset.mem_filter, hZ, hNa, hNc]
          right; right
          exact ⟨hsS, h2, by simpa [eval, h0, h1] using hcorr⟩
    have hZle : Z.card ≤ b.leaves := by
      refine le_trans (Finset.card_le_card ?_) (ihb S)
      intro s hs
      simp only [hZ, Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.2⟩
    have hNale : Na.card ≤ a.leaves := by
      refine le_trans (Finset.card_le_card ?_) (iha S)
      intro s hs
      simp only [hNa, Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.2⟩
    have hNcle : Nc.card ≤ c.leaves := by
      refine le_trans (Finset.card_le_card ?_) (ihc S)
      intro s hs
      simp only [hNc, Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.2⟩
    have hcard : W.card ≤ Z.card + (Na.card + Nc.card) := by
      have h1 : W.card ≤ (Z ∪ (Na ∪ Nc)).card := Finset.card_le_card hsub
      have h2 : (Z ∪ (Na ∪ Nc)).card ≤ Z.card + (Na ∪ Nc).card :=
        Finset.card_union_le _ _
      have h3 : (Na ∪ Nc).card ≤ Na.card + Nc.card := Finset.card_union_le _ _
      omega
    simp only [leaves]
    omega

/-- The number of leaves remaining when the middle subtree is discarded at every node. -/
def binLeaves : QueryTree n → ℕ
  | leaf _ => 1
  | node _ a _ c => a.binLeaves + c.binLeaves

/-- The number of internal nodes remaining when the middle subtree is discarded at every node. -/
def binNodes : QueryTree n → ℕ
  | leaf _ => 0
  | node _ a _ c => 1 + a.binNodes + c.binNodes

/-- The binary subtree has at most `2 ^ t.depth` leaves. -/
theorem binLeaves_le (t : QueryTree n) : t.binLeaves ≤ 2 ^ t.depth := by
  induction t with
  | leaf _ => simp [binLeaves, depth]
  | node i a b c iha ihb ihc =>
    simp only [binLeaves, depth]
    set D := max a.depth (max b.depth c.depth) with hD
    have hda : a.depth ≤ D := by rw [hD]; exact le_max_left _ _
    have hdc : c.depth ≤ D := by
      rw [hD]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have ha2 : 2 ^ a.depth ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hda
    have hc2 : 2 ^ c.depth ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hdc
    have hsum : a.binLeaves + c.binLeaves ≤ 2 ^ D + 2 ^ D := by omega
    have hpow : 2 ^ D + 2 ^ D = 2 ^ (1 + D) := by
      rw [show 1 + D = D + 1 by omega, pow_succ]
      ring
    rw [hpow] at hsum
    exact hsum

/-- The binary subtree has at most `2 ^ t.depth - 1` internal nodes. -/
theorem binNodes_le (t : QueryTree n) : t.binNodes ≤ 2 ^ t.depth - 1 := by
  induction t with
  | leaf _ => simp [binNodes, depth]
  | node i a b c iha ihb ihc =>
    simp only [binNodes, depth]
    set D := max a.depth (max b.depth c.depth) with hD
    have hda : a.depth ≤ D := by rw [hD]; exact le_max_left _ _
    have hdc : c.depth ≤ D := by
      rw [hD]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have ha2 : 2 ^ a.depth ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hda
    have hc2 : 2 ^ c.depth ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hdc
    have ha1 : 1 ≤ 2 ^ a.depth := Nat.one_le_two_pow
    have hc1 : 1 ≤ 2 ^ c.depth := Nat.one_le_two_pow
    have hia : a.binNodes ≤ 2 ^ a.depth - 1 := iha
    have hic : c.binNodes ≤ 2 ^ c.depth - 1 := ihc
    have hsum : 1 + a.binNodes + c.binNodes ≤ 2 ^ D + 2 ^ D - 1 := by omega
    have hpow : 2 ^ D + 2 ^ D = 2 ^ (1 + D) := by
      rw [show 1 + D = D + 1 by omega, pow_succ]
      ring
    rw [hpow] at hsum
    exact hsum

end QueryTree

open QueryTree

namespace WeighingMatrix

variable {n k : ℕ} (M : WeighingMatrix n k)

/-- The set of row indices correctly recovered by `t` from the weighing-matrix oracle. -/
def correctSet (t : QueryTree n) : Finset (Fin n) :=
  Finset.univ.filter (fun s => t.eval (problemFunction M s) = s)

/-- If `k ≤ n`, the number of correctly recovered rows is at most the binary leaf count plus `n
- k` times the binary node count. -/
theorem correct_card_le_bin_nat (t : QueryTree n) (hk : k ≤ n) :
    (M.correctSet t).card ≤ t.binLeaves + t.binNodes * (n - k) := by
  have haux : ∀ (t : QueryTree n) (S : Finset (Fin n)),
      (S.filter (fun s => t.eval (problemFunction M s) = s)).card ≤
        t.binLeaves + t.binNodes * (n - k) := by
    intro t
    induction t with
    | leaf s0 =>
      intro S
      have h1 : (S.filter (fun s => (QueryTree.leaf s0).eval (problemFunction M s) = s)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, eval] at ha hb
        exact ha.2.symm.trans hb.2
      simpa [binLeaves, binNodes] using h1
    | node i a b c iha ihb ihc =>
      intro S
      set W := S.filter (fun s => (QueryTree.node i a b c).eval (problemFunction M s) = s) with hW
      set Z := S.filter (fun s => branch (problemFunction M s) i = 1 ∧
        b.eval (problemFunction M s) = s) with hZ
      set Na := S.filter (fun s => branch (problemFunction M s) i = 0 ∧
        a.eval (problemFunction M s) = s) with hNa
      set Nc := S.filter (fun s => branch (problemFunction M s) i = 2 ∧
        c.eval (problemFunction M s) = s) with hNc
      have hsub : W ⊆ Z ∪ (Na ∪ Nc) := by
        intro s hs
        simp only [hW, Finset.mem_filter] at hs
        obtain ⟨hsS, hcorr⟩ := hs
        by_cases h0 : branch (problemFunction M s) i = 0
        · simp only [Finset.mem_union, Finset.mem_filter, hZ, hNa, hNc]
          right; left
          exact ⟨hsS, h0, by simpa [eval, h0] using hcorr⟩
        · by_cases h1 : branch (problemFunction M s) i = 1
          · simp only [Finset.mem_union, Finset.mem_filter, hZ, hNa, hNc]
            left
            exact ⟨hsS, h1, by simpa [eval, h0, h1] using hcorr⟩
          · have h2 : branch (problemFunction M s) i = 2 := by
              apply Fin.ext
              have hv0 : (branch (problemFunction M s) i).val ≠ 0 :=
                fun hv => h0 (Fin.ext hv)
              have hv1 : (branch (problemFunction M s) i).val ≠ 1 :=
                fun hv => h1 (Fin.ext hv)
              have hv2 : (branch (problemFunction M s) i).val < 3 := Fin.is_lt _
              omega
            simp only [Finset.mem_union, Finset.mem_filter, hZ, hNa, hNc]
            right; right
            exact ⟨hsS, h2, by simpa [eval, h0, h1] using hcorr⟩
      have hZle : Z.card ≤ n - k := by
        have hsubZ : Z ⊆ Finset.univ.filter (fun s : Fin n => M.mat s i = 0) := by
          intro s hs
          simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact (branch_eq_one_iff (problemFunction M s) i).mp hs.2.1
        have hcol := M.col_zero_card i
        rw [← hcol]
        exact Finset.card_le_card hsubZ
      have hNale : Na.card ≤ a.binLeaves + a.binNodes * (n - k) := by
        refine le_trans (Finset.card_le_card ?_) (iha S)
        intro s hs
        simp only [hNa, Finset.mem_filter] at hs ⊢
        exact ⟨hs.1, hs.2.2⟩
      have hNcle : Nc.card ≤ c.binLeaves + c.binNodes * (n - k) := by
        refine le_trans (Finset.card_le_card ?_) (ihc S)
        intro s hs
        simp only [hNc, Finset.mem_filter] at hs ⊢
        exact ⟨hs.1, hs.2.2⟩
      have hcard : W.card ≤ Z.card + (Na.card + Nc.card) := by
        have h1 : W.card ≤ (Z ∪ (Na ∪ Nc)).card := Finset.card_le_card hsub
        have h2 : (Z ∪ (Na ∪ Nc)).card ≤ Z.card + (Na ∪ Nc).card :=
          Finset.card_union_le _ _
        have h3 : (Na ∪ Nc).card ≤ Na.card + Nc.card := Finset.card_union_le _ _
        omega
      have hfin : W.card ≤
          (a.binLeaves + c.binLeaves) + (1 + a.binNodes + c.binNodes) * (n - k) := by
        have h1 : Z.card + (Na.card + Nc.card) ≤
            (n - k) + ((a.binLeaves + a.binNodes * (n - k)) +
              (c.binLeaves + c.binNodes * (n - k))) := by omega
        have h2 : (n - k) + ((a.binLeaves + a.binNodes * (n - k)) +
              (c.binLeaves + c.binNodes * (n - k))) =
            (a.binLeaves + c.binLeaves) + (1 + a.binNodes + c.binNodes) * (n - k) := by
          ring
        omega
      simpa [binLeaves, binNodes] using hfin
  have hmain := haux t Finset.univ
  simpa [correctSet] using hmain

/-- The real-valued form of the correctness bound using binary leaves, binary nodes, and column
zero counts. -/
theorem correct_card_le_bin (t : QueryTree n) (hk : k ≤ n) :
    ((M.correctSet t).card : ℝ) ≤
      (t.binLeaves : ℝ) + (t.binNodes : ℝ) * ((n : ℝ) - (k : ℝ)) := by
  have h := M.correct_card_le_bin_nat t hk
  have hcast : ((M.correctSet t).card : ℝ) ≤
      ((t.binLeaves + t.binNodes * (n - k) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  rw [Nat.cast_sub hk] at hcast
  exact hcast

/-- For positive weight `k`, at most `t.depth * k + 1` rows are correctly recovered. -/
theorem correct_card_le_depth_mul_k_nat (t : QueryTree n) (hk : 0 < k) :
    (M.correctSet t).card ≤ t.depth * k + 1 := by
  have haux : ∀ (t : QueryTree n) (S : Finset (Fin n)),
      (S.filter (fun s => t.eval (problemFunction M s) = s)).card ≤ t.depth * k + 1 := by
    intro t
    induction t with
    | leaf s0 =>
      intro S
      have h1 : (S.filter (fun s => (QueryTree.leaf s0).eval (problemFunction M s) = s)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, eval] at ha hb
        exact ha.2.symm.trans hb.2
      simpa [depth] using h1
    | node i a b c iha ihb ihc =>
      intro S
      set W := S.filter (fun s => (QueryTree.node i a b c).eval (problemFunction M s) = s) with hW
      set Z := S.filter (fun s => branch (problemFunction M s) i = 1 ∧
        b.eval (problemFunction M s) = s) with hZ
      set Nz := S.filter (fun s => branch (problemFunction M s) i ≠ 1 ∧
        (QueryTree.node i a b c).eval (problemFunction M s) = s) with hNz
      have hsub : W ⊆ Z ∪ Nz := by
        intro s hs
        simp only [hW, Finset.mem_filter] at hs
        obtain ⟨hsS, hcorr⟩ := hs
        by_cases h1 : branch (problemFunction M s) i = 1
        · simp only [Finset.mem_union, Finset.mem_filter, hZ, hNz]
          left
          exact ⟨hsS, h1, by simpa [eval, h1] using hcorr⟩
        · simp only [Finset.mem_union, Finset.mem_filter, hZ, hNz]
          right
          exact ⟨hsS, h1, hcorr⟩
      have hZle : Z.card ≤ b.depth * k + 1 := by
        refine le_trans (Finset.card_le_card ?_) (ihb S)
        intro s hs
        simp only [hZ, Finset.mem_filter] at hs ⊢
        exact ⟨hs.1, hs.2.2⟩
      have hNzle : Nz.card ≤ k := by
        have hsubNz : Nz ⊆ Finset.univ.filter (fun s : Fin n => M.mat s i ≠ 0) := by
          intro s hs
          simp only [hNz, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact fun h0 => hs.2.1 ((branch_eq_one_iff (problemFunction M s) i).mpr h0)
        have hcol := M.col_nonzero_card i
        rw [← hcol]
        exact Finset.card_le_card hsubNz
      have hcard : W.card ≤ Z.card + Nz.card := by
        have h1 : W.card ≤ (Z ∪ Nz).card := Finset.card_le_card hsub
        exact le_trans h1 (Finset.card_union_le _ _)
      have hfin : W.card ≤ (1 + max a.depth (max b.depth c.depth)) * k + 1 := by
        have hb1 : Z.card + Nz.card ≤ (b.depth * k + 1) + k :=
          Nat.add_le_add hZle hNzle
        have heq : (b.depth * k + 1) + k = (b.depth + 1) * k + 1 := by ring
        have hmul : (b.depth + 1) * k ≤ (1 + max a.depth (max b.depth c.depth)) * k := by
          apply Nat.mul_le_mul_right
          have hle : b.depth ≤ max a.depth (max b.depth c.depth) :=
            le_trans (le_max_left _ _) (le_max_right _ _)
          omega
        omega
      simpa [depth] using hfin
  have hmain := haux t Finset.univ
  simpa [correctSet] using hmain

/-- The real-valued form of the bound `t.depth * k + 1` on correctly recovered rows. -/
theorem correct_card_le_depth_mul_k (t : QueryTree n) (hk : 0 < k) :
    ((M.correctSet t).card : ℝ) ≤ (t.depth : ℝ) * (k : ℝ) + 1 := by
  have h := M.correct_card_le_depth_mul_k_nat t hk
  have hcast : ((M.correctSet t).card : ℝ) ≤ ((t.depth * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  exact hcast

/-- For `0 < ε < 1` and `0 < k ≤ n`, a tree recovering at least a `1 - ε` fraction of rows
satisfies the ternary logarithmic, linear-in-weight, and binary logarithmic lower bounds on
its depth. See [VanDam2002]. -/
theorem source_lemma2_classicalLowerBounds {n k : ℕ} (M : WeighingMatrix n k)
    (t : QueryTree n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hkn : k ≤ n) (hk : 0 < k)
    (hcorrect : (1 - ε) * (n : ℝ) ≤ ((M.correctSet t).card : ℝ)) :
    Real.log ((1 - ε) * (n : ℝ)) / Real.log 3 ≤ (t.depth : ℝ) ∧
    (1 - ε) * (n : ℝ) ≤ (t.depth : ℝ) * (k : ℝ) + 1 ∧
    Real.log ((1 - ε) * (n : ℝ) / ((n : ℝ) - (k : ℝ) + 1)) / Real.log 2 ≤
      (t.depth : ℝ) := by
  have hεpos : (0 : ℝ) < 1 - ε := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_lt_of_le hk hkn
    exact_mod_cast this
  have hpos : (0 : ℝ) < (1 - ε) * (n : ℝ) := mul_pos hεpos hnpos
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hleaves : ((M.correctSet t).card : ℝ) ≤ (t.leaves : ℝ) := by
    have h := QueryTree.correct_card_le_leaves t (problemFunction M) Finset.univ
    have h2 : ((Finset.univ.filter
        (fun s : Fin n => t.eval (problemFunction M s) = s)).card : ℝ) ≤
        (t.leaves : ℝ) := by
      exact_mod_cast h
    simpa [correctSet] using h2
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hlog3]
    have hpow : (t.leaves : ℝ) ≤ (3 : ℝ) ^ t.depth := by
      have h := QueryTree.leaves_le_three_pow t
      exact_mod_cast h
    have h3 : (1 - ε) * (n : ℝ) ≤ (3 : ℝ) ^ t.depth := le_trans hcorrect (le_trans hleaves hpow)
    have hlog := Real.log_le_log hpos h3
    rw [Real.log_pow] at hlog
    linarith
  · exact le_trans hcorrect (M.correct_card_le_depth_mul_k t hk)
  · have hbin := M.correct_card_le_bin t hkn
    have hbl : (t.binLeaves : ℝ) ≤ (2 : ℝ) ^ t.depth := by
      have h := t.binLeaves_le
      exact_mod_cast h
    have hbn : (t.binNodes : ℝ) ≤ (2 : ℝ) ^ t.depth - 1 := by
      have h := t.binNodes_le
      have hpow1 : 0 < (2 : ℕ) ^ t.depth := Nat.two_pow_pos t.depth
      have hcast : ((t.binNodes : ℕ) : ℝ) ≤ (((2 : ℕ) ^ t.depth - 1 : ℕ) : ℝ) := by
        exact_mod_cast h
      have hsub : (((2 : ℕ) ^ t.depth - 1 : ℕ) : ℝ) = (2 : ℝ) ^ t.depth - 1 := by
        rw [Nat.cast_sub hpow1]
        push_cast
        ring
      linarith
    have hnk : (0 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      linarith
    have hq : (0 : ℝ) < (n : ℝ) - (k : ℝ) + 1 := by linarith
    have hstep : ((M.correctSet t).card : ℝ) ≤
        (2 : ℝ) ^ t.depth * ((n : ℝ) - (k : ℝ) + 1) := by
      nlinarith [hbin, hbl, hbn,
        pow_pos (by norm_num : (0 : ℝ) < 2) t.depth]
    have h4 : (1 - ε) * (n : ℝ) / ((n : ℝ) - (k : ℝ) + 1) ≤ (2 : ℝ) ^ t.depth := by
      rw [div_le_iff₀ hq]
      linarith
    rw [div_le_iff₀ hlog2]
    have hlog := Real.log_le_log (div_pos hpos hq) h4
    rw [Real.log_pow] at hlog
    linarith

/-- In the Hadamard case `k = n > 0` with `0 < ε < 1`, recovering at least a `1 - ε` fraction of
rows requires depth at least `log n / log 2 + log (1 - ε) / log 2`. See [VanDam2002]. -/
theorem source_lemma2_hadamardCase {n k : ℕ} (M : WeighingMatrix n k)
    (t : QueryTree n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hkn : k = n) (hk : 0 < n)
    (hcorrect : (1 - ε) * (n : ℝ) ≤ ((M.correctSet t).card : ℝ)) :
    Real.log (n : ℝ) / Real.log 2 + Real.log (1 - ε) / Real.log 2 ≤
      (t.depth : ℝ) := by
  have hthird := (source_lemma2_classicalLowerBounds M t ε hε0 hε1
    (le_of_eq hkn) (by rw [hkn]; exact hk) hcorrect).2.2
  have h1 : (n : ℝ) - (k : ℝ) + 1 = 1 := by
    rw [hkn]
    ring
  rw [h1, div_one] at hthird
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hk
  have hepspos : (0 : ℝ) < 1 - ε := by linarith
  have hsplit : Real.log ((1 - ε) * (n : ℝ)) = Real.log (1 - ε) + Real.log (n : ℝ) :=
    Real.log_mul (ne_of_gt hepspos) (ne_of_gt hnpos)
  rw [hsplit, add_div] at hthird
  have hcomm : Real.log (1 - ε) / Real.log 2 + Real.log (n : ℝ) / Real.log 2 =
      Real.log (n : ℝ) / Real.log 2 + Real.log (1 - ε) / Real.log 2 := by ring
  rw [hcomm] at hthird
  exact hthird

end WeighingMatrix

end Qatlib.Papers.WeighMatrix00.MainResults
