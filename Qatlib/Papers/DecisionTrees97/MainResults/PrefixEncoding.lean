/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Prefix paths and Boolean register encoding

This module represents bounded-depth paths as Boolean lists and encodes them using a unary
length block followed by the path bits. It proves prefix closure, the child-length criterion,
and injectivity of `encode2n1` on paths of length at most `n`.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `validPath_prefixClosed`: proves closure of bounded-length paths under taking prefixes.
* `encode2n1_injOn`: proves injectivity of the `2 * n + 1` bit encoding on valid paths.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DecisionTrees97.MainResults

/-- The type of Boolean lists of length at most `n`. -/
def ValidPath (n : ℕ) : Type := { l : List Bool // l.length ≤ n }

/-- The condition that taking any initial segment of a list in the set produces another list in
the set. -/
def PrefixClosed (S : Set (List Bool)) : Prop :=
  ∀ l ∈ S, ∀ m : ℕ, l.take m ∈ S

/-- Boolean lists of length at most `n` form a prefix-closed set. See [FarhiGutmann1998]. -/
theorem validPath_prefixClosed (n : ℕ) :
    PrefixClosed { l : List Bool | l.length ≤ n } := by
  intro l hl m
  calc (l.take m).length = min m l.length := List.length_take
    _ ≤ l.length := Nat.min_le_right _ _
    _ ≤ n := hl

/-- Appending one Boolean child bit gives a list of length at most `n` exactly when the original
length is less than `n`. See [FarhiGutmann1998]. -/
theorem validPath_append_child (n : ℕ) (l : List Bool) (b : Bool) :
    (l ++ [b]).length ≤ n ↔ l.length < n := by
  rw [List.length_append, List.length_singleton]
  omega

/-- The Boolean register encoding with `n + 1` unary length bits followed by `n` path bits
padded with false. -/
def encode2n1 (n : ℕ) (l : List Bool) : Fin (2 * n + 1) → Bool :=
  fun i =>
    if (i : ℕ) ≤ n then decide ((i : ℕ) < l.length)
    else l.getD ((i : ℕ) - (n + 1)) false

/-- Valid paths with equal register encodings have equal lengths. -/
theorem length_eq_of_encode2n1_eq {n : ℕ} {l₁ l₂ : List Bool}
    (h₁ : l₁.length ≤ n) (h₂ : l₂.length ≤ n)
    (h : encode2n1 n l₁ = encode2n1 n l₂) : l₁.length = l₂.length := by
  apply le_antisymm
  · by_contra hle
    have hlt : l₂.length < l₁.length := Nat.lt_of_not_le hle
    have hidx : l₂.length < 2 * n + 1 := by omega
    have he := congrFun h ⟨l₂.length, hidx⟩
    have he' : decide (l₂.length < l₁.length) = decide (l₂.length < l₂.length) := by
      simpa only [encode2n1, if_pos h₂] using he
    exact absurd ((decide_eq_decide.mp he').mp hlt) (Nat.lt_irrefl _)
  · by_contra hle
    have hlt : l₁.length < l₂.length := Nat.lt_of_not_le hle
    have hidx : l₁.length < 2 * n + 1 := by omega
    have he := congrFun h ⟨l₁.length, hidx⟩
    have he' : decide (l₁.length < l₁.length) = decide (l₁.length < l₂.length) := by
      simpa only [encode2n1, if_pos h₁] using he
    exact absurd ((decide_eq_decide.mp he').mpr hlt) (Nat.lt_irrefl _)

/-- The register encoding is injective on Boolean lists of length at most `n`. See
[FarhiGutmann1998]. -/
theorem encode2n1_injOn (n : ℕ) :
    Set.InjOn (encode2n1 n) { l : List Bool | l.length ≤ n } := by
  intro l₁ h₁ l₂ h₂ h
  change l₁.length ≤ n at h₁
  change l₂.length ≤ n at h₂
  have hlen : l₁.length = l₂.length := length_eq_of_encode2n1_eq h₁ h₂ h
  have hpath : l₁ = l₂ := by
    apply List.ext_getElem hlen
    intro j hj₁ hj₂
    have hidx : n + 1 + j < 2 * n + 1 := by omega
    have hgt : ¬ (n + 1 + j ≤ n) := by omega
    have he := congrFun h ⟨n + 1 + j, hidx⟩
    simp only [encode2n1, if_neg hgt] at he
    have hsub : n + 1 + j - (n + 1) = j := by omega
    rw [hsub, List.getD_eq_getElem l₁ false hj₁, List.getD_eq_getElem l₂ false hj₂] at he
    exact he
  exact hpath

/-- The level bit at `i` in the encoding is true exactly when `i` is less than the list length,
expressed using `decide`. -/
theorem encode2n1_level_true {n : ℕ} (l : List Bool) (i : Fin (n + 1)) :
    encode2n1 n l ⟨i, by omega⟩ = decide ((i : ℕ) < l.length) := by
  simp only [encode2n1, if_pos (by omega : (i : ℕ) ≤ n)]

end Qatlib.Papers.DecisionTrees97.MainResults
