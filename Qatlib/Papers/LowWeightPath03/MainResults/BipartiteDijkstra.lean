/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LowWeightPath03.MainResults.BipartiteDijkstra

def bipartiteInitWork (n1 n2 : ℝ) : ℝ := n1 * Real.sqrt n2

def bipartiteSearchWork (n1 n2 : ℝ) : ℝ := n1 ^ 2 * Real.sqrt n2

def bipartiteUpdateWork (n1 n2 : ℝ) : ℝ := n1 ^ 2 * Real.sqrt n2

def bipartiteFinalWork (n1 n2 : ℝ) : ℝ := n2 * Real.sqrt n1

def bipartiteQuantumWork (n1 n2 : ℝ) : ℝ :=
  bipartiteSearchWork n1 n2 + bipartiteFinalWork n1 n2

def bipartiteClassicalWork (n1 n2 : ℝ) : ℝ := n1 * n2

def bipartiteMemory (n1 : ℝ) : ℝ := n1

def bipartiteClassicalMemory (n1 n2 : ℝ) : ℝ := n1 * n2

theorem bipartite_search_eq_update (n1 n2 : ℝ) :
    bipartiteSearchWork n1 n2 = bipartiteUpdateWork n1 n2 :=
  rfl

theorem bipartite_quantum_work_expand (n1 n2 : ℝ) :
    bipartiteQuantumWork n1 n2 = n1 ^ 2 * Real.sqrt n2 + n2 * Real.sqrt n1 :=
  rfl

theorem bipartite_quantum_beats_classical_iff (n1 n2 : ℝ) (h1 : 0 < n1)
    (h2 : 0 < n2) :
    bipartiteSearchWork n1 n2 < bipartiteClassicalWork n1 n2 ↔ n1 < Real.sqrt n2 := by
  have hs : 0 < Real.sqrt n2 := Real.sqrt_pos.2 h2
  have hn2 : Real.sqrt n2 * Real.sqrt n2 = n2 := by
    rw [← sq]
    exact Real.sq_sqrt h2.le
  unfold bipartiteSearchWork bipartiteClassicalWork
  constructor
  · intro h
    have h1' : n1 * (n1 * Real.sqrt n2) < n1 * n2 := by
      calc n1 * (n1 * Real.sqrt n2) = n1 ^ 2 * Real.sqrt n2 := by ring
        _ < n1 * n2 := h
    have h2' : n1 * Real.sqrt n2 < n2 :=
      (mul_lt_mul_iff_of_pos_left h1).mp h1'
    have h3 : n1 * Real.sqrt n2 < Real.sqrt n2 * Real.sqrt n2 := by
      calc n1 * Real.sqrt n2 < n2 := h2'
        _ = Real.sqrt n2 * Real.sqrt n2 := hn2.symm
    exact (mul_lt_mul_iff_of_pos_right hs).mp h3
  · intro h
    have h3 : n1 * Real.sqrt n2 < Real.sqrt n2 * Real.sqrt n2 :=
      (mul_lt_mul_iff_of_pos_right hs).mpr h
    have h3' : n1 * Real.sqrt n2 < n2 := by
      calc n1 * Real.sqrt n2 < Real.sqrt n2 * Real.sqrt n2 := h3
        _ = n2 := hn2
    have h2' : n1 * (n1 * Real.sqrt n2) < n1 * n2 :=
      (mul_lt_mul_iff_of_pos_left h1).mpr h3'
    calc n1 ^ 2 * Real.sqrt n2 = n1 * (n1 * Real.sqrt n2) := by ring
      _ < n1 * n2 := h2'

theorem bipartite_quantum_wins_of_lt_sqrt (n1 n2 : ℝ) (h1 : 0 < n1) (h2 : 0 < n2)
    (h : n1 < Real.sqrt n2) :
    bipartiteSearchWork n1 n2 < bipartiteClassicalWork n1 n2 :=
  (bipartite_quantum_beats_classical_iff n1 n2 h1 h2).mpr h

theorem bipartite_search_le_quantum_work (n1 n2 : ℝ) (h2 : 0 ≤ n2) :
    bipartiteSearchWork n1 n2 ≤ bipartiteQuantumWork n1 n2 := by
  unfold bipartiteQuantumWork
  exact le_add_of_nonneg_right (mul_nonneg h2 (Real.sqrt_nonneg n1))

theorem bipartite_memory_lt_classical (n1 n2 : ℝ) (h1 : 1 < n1) (h2 : 1 < n2) :
    bipartiteMemory n1 < bipartiteClassicalMemory n1 n2 := by
  unfold bipartiteMemory bipartiteClassicalMemory
  calc n1 = n1 * 1 := (mul_one n1).symm
    _ < n1 * n2 := mul_lt_mul_of_pos_left h2 (lt_trans zero_lt_one h1)

end Qatlib.Papers.LowWeightPath03.MainResults.BipartiteDijkstra
