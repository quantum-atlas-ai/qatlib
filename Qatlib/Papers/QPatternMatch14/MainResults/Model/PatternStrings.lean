/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite `d`-dimensional strings and pattern matching

This file formalises the basic objects of Montanaro, *Quantum pattern matching
fast on average* (arXiv:1408.1816v3), Section 1.1: a `d`-dimensional string is a
function on the grid `[n]^d`, and a pattern `P : [m]^d → Σ` matches a text
`T : [n]^d → Σ` at offset `s : [n-m+1]^d` when `P(x) = T(x+s)` for every `x`.

All results here are elementary facts about these finite objects; they carry the
combinatorial content that the paper uses implicitly and are used by the paper
layer statements of Theorems 1, 2, 5, Propositions 8, 13 and Lemmas 6, 7, 10,
11, 12.
-/

/-!
# PatternStrings

Paper-layer definitions and source results for QPatternMatch14.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.QPatternMatch14.MainResults.Model

/-- The `d`-dimensional grid `[n]^d` of coordinates. -/
abbrev Coord (d n : ℕ) := Fin d → Fin n

/-- A `d`-dimensional string of length `n` over the alphabet `A`. -/
abbrev DStr (d n : ℕ) (A : Type*) := Coord d n → A

/-- Embed the window `x : [m]^d` into the text grid `[n]^d` at offset
`s : [n-m+1]^d`, i.e. the coordinate `x + s` of the paper.  Requires `m ≤ n`. -/
def shiftIdx {d m n : ℕ} (hmn : m ≤ n)
    (s : Coord d (n - m + 1)) (x : Coord d m) : Coord d n :=
  fun i => ⟨(s i).val + (x i).val, by
    have hs : (s i).val < n - m + 1 := (s i).isLt
    have hx : (x i).val < m := (x i).isLt
    omega⟩

/-- `P` matches `T` at offset `s` when `P(x) = T(x+s)` for all `x ∈ [m]^d`. -/
def matchesAt {d m n : ℕ} {A : Type*} (hmn : m ≤ n)
    (T : DStr d n A) (P : DStr d m A) (s : Coord d (n - m + 1)) : Prop :=
  ∀ x, T (shiftIdx hmn s x) = P x

/-- The number of positions of the pattern that disagree with the text at offset
`s`; the paper's `|{x : P(x) ≠ T(x+s)}|`. -/
noncomputable def mismatchCount {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) : ℕ :=
  Fintype.card { x : Coord d m // T (shiftIdx hmn s x) ≠ P x }

/-- The number of agreeing positions `|{x : P(x) = T(x+s)}|`. -/
noncomputable def matchCount {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) : ℕ :=
  Fintype.card { x : Coord d m // T (shiftIdx hmn s x) = P x }

/-- The mismatch fraction `|{x : P(x) ≠ T(x+s)}| / m^d` of the paper. -/
noncomputable def mismatchFraction {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) : ℝ :=
  (mismatchCount hmn T P s : ℝ) / (m ^ d : ℝ)

/-- The paper's `S.ν : [n-ν+1]^d → [ν]^d → Σ`, the length-`ν` window
`window S ν s x = S (x + s)`. -/
def window {d n : ℕ} {A : Type*} (S : DStr d n A) (k : ℕ) (hk : k ≤ n)
    (s : Coord d (n - k + 1)) : DStr d k A :=
  fun z => S (fun i => ⟨(s i).val + (z i).val, by
    have hs : (s i).val < n - k + 1 := (s i).isLt
    have hz : (z i).val < k := (z i).isLt
    omega⟩)

/-- The paper's `υ(S) ≤ ν`: the length-`ν` window map of `S` is injective. -/
def injectivityLengthAtMost {d n : ℕ} {A : Type*} (S : DStr d n A) (ν : ℕ)
    (hν : ν ≤ n) : Prop :=
  Function.Injective (window S ν hν)

/-- Cardinality of the `d`-dimensional grid (arXiv:1408.1816v3, Section 1.1, p. 2). -/
theorem card_coord (d n : ℕ) : Fintype.card (Coord d n) = n ^ d := by
  simp [Coord]

/-- Agreement and disagreement counts partition `[m]^d` (arXiv:1408.1816v3, p. 3). -/
theorem matchCount_add_mismatchCount {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) :
    matchCount hmn T P s + mismatchCount hmn T P s = m ^ d := by
  rw [mismatchCount, matchCount]
  rw [Fintype.card_subtype_compl (α := Coord d m)
    (p := fun x => T (shiftIdx hmn s x) = P x)]
  rw [Nat.add_sub_cancel'
    (Fintype.card_subtype_le (α := Coord d m)
      (p := fun x => T (shiftIdx hmn s x) = P x))]
  rw [card_coord]

/-- A pattern matches exactly when no position disagrees (arXiv:1408.1816v3, p. 3). -/
theorem matchesAt_iff_mismatchCount_eq_zero {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) :
    matchesAt hmn T P s ↔ mismatchCount hmn T P s = 0 := by
  constructor
  · intro h
    unfold mismatchCount
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => absurd (h x.1) x.2⟩
  · intro h x
    by_contra hx
    have : 0 < mismatchCount hmn T P s := by
      unfold mismatchCount
      rw [Fintype.card_pos_iff]
      exact ⟨⟨x, hx⟩⟩
    omega

/-- The mismatch count is bounded by the number of pattern positions (arXiv:1408.1816v3, p. 3). -/
theorem mismatchCount_le_card {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) :
    mismatchCount hmn T P s ≤ m ^ d := by
  have h := Fintype.card_subtype_le (α := Coord d m)
    (p := fun x => T (shiftIdx hmn s x) ≠ P x)
  rw [← card_coord d m]
  exact h

/-- The mismatch fraction is nonnegative (arXiv:1408.1816v3, p. 3). -/
theorem mismatchFraction_nonneg {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) :
    0 ≤ mismatchFraction hmn T P s := by
  unfold mismatchFraction
  positivity

/-- The mismatch fraction is at most one (arXiv:1408.1816v3, p. 3). -/
theorem mismatchFraction_le_one {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) :
    mismatchFraction hmn T P s ≤ 1 := by
  unfold mismatchFraction
  rcases Nat.eq_zero_or_pos (m ^ d) with h0 | hpos
  · have hc : mismatchCount hmn T P s = 0 := by
      have := mismatchCount_le_card hmn T P s
      omega
    have hcast : ((m ^ d : ℕ) : ℝ) = 0 := by exact_mod_cast h0
    have hpow : ((m : ℝ) ^ d) = 0 := by rw [← Nat.cast_pow, hcast]
    rw [hc, hpow]
    simp
  · have hR : (0 : ℝ) < (m ^ d : ℝ) := by exact_mod_cast hpos
    rw [div_le_one hR]
    exact_mod_cast mismatchCount_le_card hmn T P s

/-- If every position matches, the mismatch fraction vanishes (arXiv:1408.1816v3, p. 3). -/
theorem mismatchFraction_eq_zero_of_matches {d m n : ℕ} {A : Type*} [DecidableEq A]
    (hmn : m ≤ n) (T : DStr d n A) (P : DStr d m A)
    (s : Coord d (n - m + 1)) (h : matchesAt hmn T P s) :
    mismatchFraction hmn T P s = 0 := by
  unfold mismatchFraction
  rw [(matchesAt_iff_mismatchCount_eq_zero hmn T P s).1 h]
  simp

end Qatlib.Papers.QPatternMatch14.MainResults.Model
