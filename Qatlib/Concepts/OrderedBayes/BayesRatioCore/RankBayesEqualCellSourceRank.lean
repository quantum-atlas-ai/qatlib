/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellDefs
set_option warningAsError false

noncomputable section

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped Classical

def feasible {n : ℕ} (x : Fin n → ℝ) (s : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun c => s ≤ x c)

def lastTrue {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c) : Fin n :=
  (feasible x s).max' (by
    obtain ⟨c,hc⟩ := h
    exact ⟨c,by simp [feasible,hc]⟩)

theorem lastTrue_mem {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c) :
    s ≤ x (lastTrue x s h) := by
  have hm := Finset.max'_mem (feasible x s) (by
    obtain ⟨c,hc⟩ := h
    exact ⟨c,by simp [feasible,hc]⟩)
  exact (Finset.mem_filter.mp hm).2

theorem source_threshold {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c)
    (hx : Antitone x) (c : Fin n) : s ≤ x c ↔ c ≤ lastTrue x s h := by
  constructor
  · intro hc
    exact Finset.le_max' (feasible x s) c (by simp [feasible,hc])
  · intro hc
    exact (lastTrue_mem x s h).trans (hx hc)

theorem source_rank_unique {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (h : ∃ c, s ≤ x c)
    (hx : Antitone x) (j : Fin n) (hj : ∀ c, s ≤ x c ↔ c ≤ j) :
    j = lastTrue x s h := by
  apply le_antisymm
  · exact (source_threshold x s h hx j).mp ((hj j).mpr le_rfl)
  · exact (hj _).mp (lastTrue_mem x s h)

def closedCell {n : ℕ} (x : Fin (n+1) → ℝ) (s : ℝ) (j : Fin n) : Prop :=
  s ≤ x j.castSucc ∧ x j.succ ≤ s

theorem closed_cells_overlap :
    closedCell ![(30 : ℝ),20,10] 20 (0 : Fin 2) ∧
    closedCell ![(30 : ℝ),20,10] 20 (1 : Fin 2) ∧ (0 : Fin 2) ≠ 1 := by
  change ((20 : ℝ) ≤ 30 ∧ (20 : ℝ) ≤ 20) ∧
    ((20 : ℝ) ≤ 20 ∧ (10 : ℝ) ≤ 20) ∧ (0 : Fin 2) ≠ 1
  norm_num

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
