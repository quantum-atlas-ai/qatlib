/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Work and memory expressions for bipartite quantum Dijkstra

This module defines the search, update, finalization, and memory expressions for the bipartite
quantum Dijkstra analysis of [Heiligman2003]. It expands the total quantum work and
characterizes exactly when the search term is smaller than the classical work expression.

## Main statements

* `bipartite_quantum_work_expand`: Expands total quantum work as `n1 ^ 2 * sqrt n2 + n2 * sqrt
  n1`.
* `bipartite_quantum_beats_classical_iff`: Compares the search term with classical work for
  positive part sizes.
* `bipartite_memory_lt_classical`: Compares the memory expressions when both part sizes exceed
  one.

## References

* [Heiligman, 2003][Heiligman2003]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LowWeightPath03.MainResults.BipartiteDijkstra

/-- The bipartite initialization work expression `n1 * Real.sqrt n2`. -/
def bipartiteInitWork (n1 n2 : ℝ) : ℝ := n1 * Real.sqrt n2

/-- The bipartite quantum search work expression `n1 ^ 2 * Real.sqrt n2`. -/
def bipartiteSearchWork (n1 n2 : ℝ) : ℝ := n1 ^ 2 * Real.sqrt n2

/-- The bipartite quantum update work expression `n1 ^ 2 * Real.sqrt n2`. -/
def bipartiteUpdateWork (n1 n2 : ℝ) : ℝ := n1 ^ 2 * Real.sqrt n2

/-- The bipartite finalization work expression `n2 * Real.sqrt n1`. -/
def bipartiteFinalWork (n1 n2 : ℝ) : ℝ := n2 * Real.sqrt n1

/-- The total bipartite quantum work expression, defined as the search work plus the
finalization work. -/
def bipartiteQuantumWork (n1 n2 : ℝ) : ℝ :=
  bipartiteSearchWork n1 n2 + bipartiteFinalWork n1 n2

/-- The bipartite classical work comparison expression `n1 * n2`. -/
def bipartiteClassicalWork (n1 n2 : ℝ) : ℝ := n1 * n2

/-- The bipartite quantum memory comparison expression `n1`. -/
def bipartiteMemory (n1 : ℝ) : ℝ := n1

/-- The bipartite classical memory comparison expression `n1 * n2`. -/
def bipartiteClassicalMemory (n1 n2 : ℝ) : ℝ := n1 * n2

/-- The bipartite quantum search and update work expressions are equal [Heiligman2003]. -/
theorem bipartite_search_eq_update (n1 n2 : ℝ) :
    bipartiteSearchWork n1 n2 = bipartiteUpdateWork n1 n2 :=
  rfl

/-- The total bipartite quantum work expression equals `n1 ^ 2 * Real.sqrt n2 + n2 * Real.sqrt
n1` [Heiligman2003]. -/
theorem bipartite_quantum_work_expand (n1 n2 : ℝ) :
    bipartiteQuantumWork n1 n2 = n1 ^ 2 * Real.sqrt n2 + n2 * Real.sqrt n1 :=
  rfl

/-- For positive `n1` and `n2`, the quantum search work is strictly smaller than the classical
work exactly when `n1 < Real.sqrt n2` [Heiligman2003]. -/
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

/-- For positive part sizes with `n1 < Real.sqrt n2`, the bipartite quantum search work is
strictly smaller than the classical work [Heiligman2003]. -/
theorem bipartite_quantum_wins_of_lt_sqrt (n1 n2 : ℝ) (h1 : 0 < n1) (h2 : 0 < n2)
    (h : n1 < Real.sqrt n2) :
    bipartiteSearchWork n1 n2 < bipartiteClassicalWork n1 n2 :=
  (bipartite_quantum_beats_classical_iff n1 n2 h1 h2).mpr h

/-- For nonnegative `n2`, the bipartite search work is at most the total quantum work
[Heiligman2003]. -/
theorem bipartite_search_le_quantum_work (n1 n2 : ℝ) (h2 : 0 ≤ n2) :
    bipartiteSearchWork n1 n2 ≤ bipartiteQuantumWork n1 n2 := by
  unfold bipartiteQuantumWork
  exact le_add_of_nonneg_right (mul_nonneg h2 (Real.sqrt_nonneg n1))

/-- When both part sizes exceed one, the quantum memory expression is strictly smaller than the
classical memory expression [Heiligman2003]. -/
theorem bipartite_memory_lt_classical (n1 n2 : ℝ) (h1 : 1 < n1) (h2 : 1 < n2) :
    bipartiteMemory n1 < bipartiteClassicalMemory n1 n2 := by
  unfold bipartiteMemory bipartiteClassicalMemory
  calc n1 = n1 * 1 := (mul_one n1).symm
    _ < n1 * n2 := mul_lt_mul_of_pos_left h2 (lt_trans zero_lt_one h1)

end Qatlib.Papers.LowWeightPath03.MainResults.BipartiteDijkstra
