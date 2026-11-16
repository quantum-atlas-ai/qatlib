/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Bitwise
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Closed refinement support for the star-decomposition construction

Source: arXiv:1003.3683v2, Lemma 2, pp. 7--8; recovered from legacy
commit 9182ca0aca06c3e45b933ef9064bb7e805ebdb6e, SourceVertexColoring.
These are the properness and finite ancestor-chain lemmas needed by the
closed support of Theorem 4. No claim that the recurrence reaches six colors
in log-star rounds is imported or assumed here. Root output uses its current
bit at position zero, including singleton and empty vertex sets.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.StarDecompSim10.ForestColors

open Finset

variable {N : ℕ}

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

/-- The index of the most significant set bit of a positive number, and `0`
at zero.  Used as the paper's "first bit at which the two colours differ". -/
def msb (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else Classical.choose (Nat.exists_most_significant_bit h)

/-- The chosen bit is set. -/
theorem msbBit (n : ℕ) (h : n ≠ 0) : n.testBit (msb n) = true := by
  unfold msb
  rw [dite_eq_right h]
  exact (Classical.choose_spec (Nat.exists_most_significant_bit h)).1

/-- The index of the most significant differing bit of `a` and `b`. -/
def topDiff (a b : ℕ) : ℕ := msb (a ^^^ b)

/-- Distinct numbers differ at their most significant differing bit. -/
theorem diffBit {a b : ℕ} (h : a ≠ b) :
    a.testBit (topDiff a b) ≠ b.testBit (topDiff a b) := by
  have hxor : a ^^^ b ≠ 0 := Nat.xor_ne_zero_iff.mpr h
  have hspec : (a ^^^ b).testBit (topDiff a b) = true := msbBit _ hxor
  rw [Nat.testBit_xor] at hspec
  intro heq
  rw [heq] at hspec
  simp at hspec

/-- The bit value at position `k`, as `0` or `1`. -/
def bitVal (a k : ℕ) : ℕ := if a.testBit k then 1 else 0

/-- A test-bit value is strictly less than two. -/
theorem bitLtTwo (a k : ℕ) : bitVal a k < 2 := by
  unfold bitVal
  split <;> norm_num

/-- Distinct test bits give distinct numerical bit values. -/
theorem bitNe {a b k : ℕ} (h : a.testBit k ≠ b.testBit k) :
    bitVal a k ≠ bitVal b k := by
  unfold bitVal
  cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp_all

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
theorem refineProper (parent : Fin N → Option (Fin N)) (κ : Fin N → ℕ)
    (hproper : ∀ v p, parent v = some p → κ v ≠ κ p) :
    ∀ v p, parent v = some p → refineVal parent κ v ≠ refineVal parent κ p := by
  intro v p hvp
  have hv_ne : κ v ≠ κ p := hproper v p hvp
  have hk : (κ v).testBit (topDiff (κ v) (κ p)) ≠ (κ p).testBit (topDiff (κ v) (κ p)) :=
    diffBit hv_ne
  have hvr : refineVal parent κ v =
      2 * topDiff (κ v) (κ p) + bitVal (κ v) (topDiff (κ v) (κ p)) := by
    simp [refineVal, hvp]
  cases hp : parent p with
  | none =>
      have hpr : refineVal parent κ p = bitVal (κ p) 0 := by simp [refineVal, hp]
      rw [hvr, hpr]
      intro heq
      have hb1 : bitVal (κ v) (topDiff (κ v) (κ p)) < 2 := bitLtTwo _ _
      have hb0 : bitVal (κ p) 0 < 2 := bitLtTwo _ _
      have hk0 : topDiff (κ v) (κ p) = 0 := by omega
      have hbb : bitVal (κ v) (topDiff (κ v) (κ p)) = bitVal (κ p) 0 := by omega
      have hbit : bitVal (κ v) 0 = bitVal (κ p) 0 := by rwa [hk0] at hbb
      have hk0' : (κ v).testBit 0 ≠ (κ p).testBit 0 := by rwa [hk0] at hk
      exact bitNe hk0' hbit
  | some q =>
      have hpr : refineVal parent κ p =
          2 * topDiff (κ p) (κ q) + bitVal (κ p) (topDiff (κ p) (κ q)) := by
        simp [refineVal, hp]
      rw [hvr, hpr]
      intro heq
      have hb1 : bitVal (κ v) (topDiff (κ v) (κ p)) < 2 := bitLtTwo _ _
      have hb2 : bitVal (κ p) (topDiff (κ p) (κ q)) < 2 := bitLtTwo _ _
      have hkk : topDiff (κ v) (κ p) = topDiff (κ p) (κ q) := by omega
      have hbb : bitVal (κ v) (topDiff (κ v) (κ p)) =
          bitVal (κ p) (topDiff (κ p) (κ q)) := by omega
      have hbit : bitVal (κ v) (topDiff (κ v) (κ p)) =
          bitVal (κ p) (topDiff (κ v) (κ p)) := by rw [hbb, hkk]
      exact bitNe hk hbit

/-- The colour after `j` rounds, starting from the label colouring. -/
def colorAt (parent : Fin N → Option (Fin N)) : ℕ → Fin N → ℕ
  | 0 => fun v => v.val
  | j + 1 => fun v => refineVal parent (colorAt parent j) v

/-- Every round preserves properness. -/
theorem colorProper {parent : Fin N → Option (Fin N)}
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
      exact refineProper parent (colorAt parent j) ih

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
theorem reachBound (parent : Fin N → Option (Fin N)) (j : ℕ) (v : Fin N) :
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

end Qatlib.Papers.StarDecompSim10.ForestColors
