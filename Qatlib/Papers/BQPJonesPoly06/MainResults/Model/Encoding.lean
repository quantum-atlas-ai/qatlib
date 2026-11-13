/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Amplitude

/-!
# Crossing bounds for concatenated braid words

This module concatenates lists of braid words and counts their crossings. Crossing counts add
exactly, uniform per-word bounds give a length-times-bound estimate, and polynomial per-word
bounds yield a polynomial bound of one higher degree. See [AharonovArad2011].

## Main statements

* `numCrossings_concat`: the concatenated crossing count is the sum of counts.
* `numCrossings_concat_le`: a uniform bound multiplies by list length.
* `numCrossings_concat_poly`: a polynomial word bound yields a polynomial total bound.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

variable {n : ℕ}

/-- Concatenate the crossing lists of a list of braid words in order. -/
def concatWords : List (BraidWord n) → BraidWord n
  | [] => ⟨[]⟩
  | b :: rest => ⟨b.crossings ++ (concatWords rest).crossings⟩

/-- Concatenating an empty list of braid words gives the empty braid word. -/
@[simp]
theorem concatWords_nil : concatWords ([] : List (BraidWord n)) = ⟨[]⟩ := rfl

/-- Concatenating a nonempty list appends the head’s crossings to the crossings of the
concatenated tail. -/
@[simp]
theorem concatWords_cons (b : BraidWord n) (rest : List (BraidWord n)) :
    concatWords (b :: rest) = ⟨b.crossings ++ (concatWords rest).crossings⟩ := rfl

/-- The crossing count of concatenated braid words equals the sum of their individual crossing
counts. -/
theorem numCrossings_concat (l : List (BraidWord n)) :
    (concatWords l).numCrossings = (l.map BraidWord.numCrossings).sum := by
  induction l with
  | nil => simp [concatWords, BraidWord.numCrossings]
  | cons b rest ih =>
      simp only [concatWords, BraidWord.numCrossings, List.map_cons, List.sum_cons,
        List.length_append] at ih ⊢
      omega

/-- If each braid word has at most `M` crossings, their concatenation has at most `l.length * M`
crossings. -/
theorem numCrossings_concat_le (l : List (BraidWord n)) {M : ℕ}
    (h : ∀ b ∈ l, b.numCrossings ≤ M) :
    (concatWords l).numCrossings ≤ l.length * M := by
  rw [numCrossings_concat]
  induction l with
  | nil => simp
  | cons b rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hb : b.numCrossings ≤ M := h b (by simp)
      have hrest : ∀ c ∈ rest, c.numCrossings ≤ M := fun c hc => h c (by simp [hc])
      have hrec := ih hrest
      calc b.numCrossings + (List.map BraidWord.numCrossings rest).sum
          ≤ M + rest.length * M := Nat.add_le_add hb hrec
        _ = (rest.length + 1) * M := by ring

/-- If each braid word has at most `C * (l.length + 1) ^ d` crossings, their concatenation has
at most `C * (l.length + 1) ^ (d + 1)` crossings. -/
theorem numCrossings_concat_poly (l : List (BraidWord n)) {C d : ℕ}
    (h : ∀ b ∈ l, b.numCrossings ≤ C * (l.length + 1) ^ d) :
    (concatWords l).numCrossings ≤ C * (l.length + 1) ^ (d + 1) := by
  have h1 := numCrossings_concat_le l h
  calc (concatWords l).numCrossings
      ≤ l.length * (C * (l.length + 1) ^ d) := h1
    _ ≤ (l.length + 1) * (C * (l.length + 1) ^ d) :=
          Nat.mul_le_mul_right _ (by omega)
    _ = C * (l.length + 1) ^ (d + 1) := by
          rw [pow_succ]
          ring

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
