/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Qatlib.Papers.WeighMatrix00.MainResults.SLSLegendre

/-!
# Classical lower bounds for shifted Legendre sequences

The decision trees `SLSTree` branch on nonzero quadratic-character values and return the shift
immediately on a zero response. Counting terminal outputs bounds the number of correctly
recovered shifts and gives the logarithmic depth estimates in `source_lemma3_slsLowerBound`.

This development forms part of the formalization of [VanDam2002].

## Main statements

* `SLSTree`: A shifted Legendre sequence query tree with output leaves and two subtrees for the
  nonzero responses.
* `source_lemma3_slsLowerBound`: Over a finite field of characteristic different from two and
  for `0 < ε < 1`, recovering at least a `1 - ε` fraction of shifts gives the two stated
  base-two logarithmic lower bounds on tree depth.

## References

* [van Dam, 2002][VanDam2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A shifted Legendre sequence query tree with output leaves and two subtrees for the nonzero
responses. -/
inductive SLSTree (F : Type*) where

  | leaf (s : F) : SLSTree F

  | node (i : F) (minus plus : SLSTree F) : SLSTree F

namespace SLSTree

/-- The maximum number of query nodes along a path in a shifted Legendre sequence tree. -/
def depth : SLSTree F → ℕ
  | leaf _ => 0
  | node _ m p => 1 + max m.depth p.depth

/-- Count terminal outputs, including the immediate zero-response output at each query node. -/
def leaves : SLSTree F → ℕ
  | leaf _ => 1
  | node _ m p => 1 + m.leaves + p.leaves

/-- Evaluate the shifted quadratic-character oracle, returning `-i` on a zero response and
following the appropriate subtree otherwise. -/
def eval : SLSTree F → F → F
  | leaf s0, _ => s0
  | node i m p, s =>
      if quadraticChar F (i + s) = 0 then -i
      else if quadraticChar F (i + s) = 1 then p.eval s else m.eval s

/-- A zero quadratic-character response at index `i` makes the node return `-i`. -/
theorem eval_node_zero (i : F) (m p : SLSTree F) (s : F)
    (h : quadraticChar F (i + s) = 0) : (node i m p).eval s = -i := by
  simp only [eval]
  rw [if_pos h]

/-- A nonzero quadratic-character response equal to one selects the plus subtree. -/
theorem eval_node_plus (i : F) (m p : SLSTree F) (s : F)
    (h0 : quadraticChar F (i + s) ≠ 0) (h1 : quadraticChar F (i + s) = 1) :
    (node i m p).eval s = p.eval s := by
  simp only [eval]
  rw [if_neg h0, if_pos h1]

/-- A quadratic-character response unequal to zero and one selects the minus subtree. -/
theorem eval_node_minus (i : F) (m p : SLSTree F) (s : F)
    (h0 : quadraticChar F (i + s) ≠ 0) (h1 : quadraticChar F (i + s) ≠ 1) :
    (node i m p).eval s = m.eval s := by
  simp only [eval]
  rw [if_neg h0, if_neg h1]

/-- The number of terminal outputs is at most `2 ^ (t.depth + 1) - 1`. -/
theorem leaves_le (t : SLSTree F) : t.leaves ≤ 2 ^ (t.depth + 1) - 1 := by
  induction t with
  | leaf _ => simp [leaves, depth]
  | node i m p ihm ihp =>
    simp only [leaves, depth]
    set D := max m.depth p.depth with hD
    have hmd : m.depth ≤ D := by rw [hD]; exact le_max_left _ _
    have hpd : p.depth ≤ D := by rw [hD]; exact le_max_right _ _
    have hm2 : 2 ^ (m.depth + 1) ≤ 2 ^ (D + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp2 : 2 ^ (p.depth + 1) ≤ 2 ^ (D + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 1 ≤ 2 ^ (D + 1) := Nat.one_le_two_pow
    have hmle : m.leaves ≤ 2 ^ (D + 1) - 1 := le_trans ihm (by omega)
    have hple : p.leaves ≤ 2 ^ (D + 1) - 1 := le_trans ihp (by omega)
    have hdouble : 2 ^ (D + 1) + 2 ^ (D + 1) = 2 ^ (D + 2) := by
      rw [show D + 2 = D + 1 + 1 by omega, pow_succ]
      ring
    have hle : 1 + m.leaves + p.leaves ≤ 2 ^ (D + 1) + 2 ^ (D + 1) - 1 := by omega
    rw [hdouble] at hle
    have hgoal : 2 ^ (D + 2) = 2 ^ (1 + (max m.depth p.depth + 1)) := by
      rw [hD]
      congr 1
      omega
    rw [hgoal] at hle
    exact hle

/-- The finite set of shifts recovered correctly by the tree. -/
def correctSet (t : SLSTree F) : Finset F :=
  Finset.univ.filter (fun s => t.eval s = s)

/-- At most `t.leaves` elements of any candidate set are recovered correctly. -/
theorem correct_card_le_leaves_aux (t : SLSTree F) (S : Finset F) :
    (S.filter (fun s => t.eval s = s)).card ≤ t.leaves := by
  induction t generalizing S with
  | leaf s0 =>
    have h1 : (S.filter (fun s => (SLSTree.leaf s0).eval s = s)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter, eval] at ha hb
      exact ha.2.symm.trans hb.2
    simpa [leaves] using h1
  | node i m p ihm ihp =>
    set W := S.filter (fun s => (SLSTree.node i m p).eval s = s) with hW
    set Z := S.filter (fun s => quadraticChar F (i + s) = 0) with hZ
    set Pm := S.filter (fun s => quadraticChar F (i + s) ≠ 0 ∧
      quadraticChar F (i + s) ≠ 1 ∧ m.eval s = s) with hPm
    set Pp := S.filter (fun s => quadraticChar F (i + s) = 1 ∧ p.eval s = s) with hPp
    have hsub : W ⊆ Z ∪ (Pm ∪ Pp) := by
      intro s hs
      simp only [hW, Finset.mem_filter] at hs
      obtain ⟨hsS, hcorr⟩ := hs
      by_cases h0 : quadraticChar F (i + s) = 0
      · simp only [Finset.mem_union, Finset.mem_filter, hZ, hPm, hPp]
        left
        exact ⟨hsS, h0⟩
      · by_cases h1 : quadraticChar F (i + s) = 1
        · simp only [Finset.mem_union, Finset.mem_filter, hZ, hPm, hPp]
          right; right
          exact ⟨hsS, h1, (eval_node_plus i m p s h0 h1).symm.trans hcorr⟩
        · simp only [Finset.mem_union, Finset.mem_filter, hZ, hPm, hPp]
          right; left
          exact ⟨hsS, h0, h1, (eval_node_minus i m p s h0 h1).symm.trans hcorr⟩
    have hZle : Z.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [hZ, Finset.mem_filter] at ha hb
      have ha' : a = -i := by
        have h : i + a = 0 := quadraticChar_eq_zero_iff.mp ha.2
        have hai : i = -a := add_eq_zero_iff_eq_neg.mp h
        rw [hai]
        ring
      have hb' : b = -i := by
        have h : i + b = 0 := quadraticChar_eq_zero_iff.mp hb.2
        have hbi : i = -b := add_eq_zero_iff_eq_neg.mp h
        rw [hbi]
        ring
      rw [ha', hb']
    have hPmle : Pm.card ≤ m.leaves := by
      refine le_trans (Finset.card_le_card ?_) (ihm S)
      intro s hs
      simp only [hPm, Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.2.2⟩
    have hPple : Pp.card ≤ p.leaves := by
      refine le_trans (Finset.card_le_card ?_) (ihp S)
      intro s hs
      simp only [hPp, Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.2⟩
    have hcard : W.card ≤ Z.card + (Pm.card + Pp.card) := by
      have h1 : W.card ≤ (Z ∪ (Pm ∪ Pp)).card := Finset.card_le_card hsub
      have h2 : (Z ∪ (Pm ∪ Pp)).card ≤ Z.card + (Pm ∪ Pp).card :=
        Finset.card_union_le _ _
      have h3 : (Pm ∪ Pp).card ≤ Pm.card + Pp.card := Finset.card_union_le _ _
      omega
    simp only [leaves]
    omega

/-- The cardinality of the set of correctly recovered shifts is bounded by the terminal-output
count. -/
theorem correct_card_le_leaves (t : SLSTree F) : t.correctSet.card ≤ t.leaves := by
  have h := correct_card_le_leaves_aux t Finset.univ
  simpa [correctSet] using h

end SLSTree

open SLSTree

/-- Over a finite field of characteristic different from two and for `0 < ε < 1`, recovering at
least a `1 - ε` fraction of shifts gives the two stated base-two logarithmic lower bounds on
tree depth. See [VanDam2002]. -/
theorem source_lemma3_slsLowerBound (hF : ringChar F ≠ 2) (hq : 1 < Fintype.card F)
    (t : SLSTree F) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hcorrect : (1 - ε) * (Fintype.card F : ℝ) ≤ (t.correctSet.card : ℝ)) :
    Real.log ((1 - ε) * (Fintype.card F : ℝ)) / Real.log 2 - 1 ≤ (t.depth : ℝ) ∧
    Real.log (Fintype.card F : ℝ) / Real.log 2 +
      Real.log ((1 - ε) / 2) / Real.log 2 ≤ (t.depth : ℝ) := by
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hq)
  have heps : (0 : ℝ) < 1 - ε := by linarith
  have hpos : (0 : ℝ) < (1 - ε) * (Fintype.card F : ℝ) := mul_pos heps hq0

  have hleaves : (t.correctSet.card : ℝ) ≤ (t.leaves : ℝ) := by
    exact_mod_cast t.correct_card_le_leaves
  have hpow : (t.leaves : ℝ) ≤ (2 : ℝ) ^ (t.depth + 1) - 1 := by
    have h := t.leaves_le
    have hcast : (t.leaves : ℝ) ≤ ((2 : ℕ) ^ (t.depth + 1) : ℝ) - 1 := by
      have h1 : (t.leaves : ℝ) ≤ (((2 : ℕ) ^ (t.depth + 1) - 1 : ℕ) : ℝ) := by
        exact_mod_cast h
      have h2 : (((2 : ℕ) ^ (t.depth + 1) - 1 : ℕ) : ℝ) =
          ((2 : ℕ) ^ (t.depth + 1) : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_two_pow)]
        simp
      linarith
    simpa using hcast
  have hchain : (1 - ε) * (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ (t.depth + 1) := by
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (t.depth + 1) := by positivity
    linarith
  have hlog := Real.log_le_log hpos hchain
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmain : Real.log ((1 - ε) * (Fintype.card F : ℝ)) / Real.log 2 ≤ (t.depth : ℝ) + 1 := by
    rw [div_le_iff₀ hlog2]
    push_cast at hlog ⊢
    linarith
  constructor
  · linarith
  · have heq : Real.log (Fintype.card F : ℝ) / Real.log 2 +
        Real.log ((1 - ε) / 2) / Real.log 2 =
        Real.log ((1 - ε) * (Fintype.card F : ℝ)) / Real.log 2 - 1 := by
      have h1 : (1 - ε) ≠ 0 := ne_of_gt heps
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have h3 : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hq0
      rw [← add_div, Real.log_div h1 h2, Real.log_mul h1 h3]
      field_simp
      ring
    rw [heq]
    linarith

end Qatlib.Papers.WeighMatrix00.MainResults
