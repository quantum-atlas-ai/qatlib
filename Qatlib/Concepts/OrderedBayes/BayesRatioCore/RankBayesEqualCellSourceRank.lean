/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellDefs

/-!
# Unique threshold ranks and overlapping closed cells

This module isolates the rank convention for a descending source sequence in ordered search
[BenOrHassidim2007]. `feasible` collects the indices whose values meet a threshold, and
`lastTrue` selects the greatest such index when one exists. For an antitone sequence,
`source_threshold` characterizes this index by all threshold comparisons.

`source_rank_unique` proves uniqueness of the resulting comparison rank. In contrast,
`closedCell` uses two inclusive endpoint inequalities, and `closed_cells_overlap` gives an
explicit boundary belonging to two distinct cells.

## Main statements

* `source_threshold`: threshold truth is equivalent to lying at or before `lastTrue`.
* `source_rank_unique`: uniqueness of the rank with that comparison pattern.
* `closed_cells_overlap`: adjacent closed cells can share a boundary value.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

noncomputable section

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped Classical

/-- The finite set of indices whose source values are at least the threshold. -/
def feasible {n : ℕ} (x : Fin n → ℝ) (s : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun c => s ≤ x c)

/-- The greatest index whose source value is at least the threshold, given that such an index
exists. -/
def lastTrue {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c) : Fin n :=
  (feasible x s).max' (by
    obtain ⟨c,hc⟩ := h
    exact ⟨c,by simp [feasible,hc]⟩)

/-- The source value at `lastTrue` is at least the threshold. -/
theorem lastTrue_mem {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c) :
    s ≤ x (lastTrue x s h) := by
  have hm := Finset.max'_mem (feasible x s) (by
    obtain ⟨c,hc⟩ := h
    exact ⟨c,by simp [feasible,hc]⟩)
  exact (Finset.mem_filter.mp hm).2

/-- For an antitone source sequence, a value meets the threshold exactly when its index is at
most the greatest index that meets it. -/
theorem source_threshold {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c)
    (hx : Antitone x) (c : Fin n) : s ≤ x c ↔ c ≤ lastTrue x s h := by
  constructor
  · intro hc
    exact Finset.le_max' (feasible x s) c (by simp [feasible,hc])
  · intro hc
    exact (lastTrue_mem x s h).trans (hx hc)

/-- For an antitone source sequence, any rank characterizing all true threshold comparisons
equals `lastTrue`. -/
theorem source_rank_unique {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c)
    (hx : Antitone x) (j : Fin n) (hj : ∀ c, s ≤ x c ↔ c ≤ j) :
    j = lastTrue x s h := by
  apply le_antisymm
  · exact (source_threshold x s h hx j).mp ((hj j).mpr le_rfl)
  · exact (hj _).mp (lastTrue_mem x s h)

/-- The threshold lies between the two consecutive source values delimiting a cell, with both
endpoints included. -/
def closedCell {n : ℕ} (x : Fin (n+1) → ℝ) (s : ℝ) (j : Fin n) : Prop :=
  s ≤ x j.castSucc ∧ x j.succ ≤ s

/-- The threshold 20 lies in both distinct adjacent closed cells of the source sequence 30, 20,
10. -/
theorem closed_cells_overlap :
    closedCell ![(30 : ℝ),20,10] 20 (0 : Fin 2) ∧
    closedCell ![(30 : ℝ),20,10] 20 (1 : Fin 2) ∧ (0 : Fin 2) ≠ 1 := by
  change ((20 : ℝ) ≤ 30 ∧ (20 : ℝ) ≤ 20) ∧
    ((20 : ℝ) ≤ 20 ∧ (10 : ℝ) ≤ 20) ∧ (0 : Fin 2) ≠ 1
  norm_num

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
