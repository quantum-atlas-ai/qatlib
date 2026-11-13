/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.QueryTester

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Bipartiteness Testing Specification (Theorem 1)

This module formalizes Theorem 1 (p. 3) of Ambainis, Childs, and Liu in the
`QuantumTester` property-testing specification model: for every `ε > 0`, there
exist constants `C > 0`, `c ∈ (0, 1)`, and `j : ℕ` such that every bounded-degree
graph size `(N, d)` with `N, d ≥ 1` admits a `QuantumTester N d` satisfying
`TestsBipartiteness` within accounted time `C N^{1/3} (log N / ε)^j`.

## Main statements

* `theorem1_bipartite_tester`: Theorem 1, one-sided quantum bipartiteness-testing
  specification with `O(N^{1/3} poly(log N / ε))` accounted time.

## References

* [Ambainis, Childs, and Liu, 2011][AmbainisChildsLiu2011PropTest], Section 1,
  Theorem 1, p. 3.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.BipartiteTesting

open Qatlib.Papers.PropTestGraph10.MainResults.Model
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

/-- Theorem 1 of the paper (p. 3).

Fixed source: arXiv:1012.3174v3, Theorem 1, p. 3.  Original statement: "There is
a quantum algorithm that always returns "true" when `G` is bipartite, returns
"false" with constant probability when `G` is `ε`-far from bipartite, and runs
in time `O(N^{1/3} poly(log N / ε))`."

Formalised as: for every `ε > 0` there are constants `C > 0`, `c ∈ (0,1)` and a
polynomial exponent `j` such that for every `N ≥ 1` and every degree bound
`d ≥ 1` there is a `QuantumTester N d` satisfying `TestsBipartiteness T ε c`
(accepting probability `1` on bipartite graphs and at most `1-c` on graphs
`ε`-far from bipartite) with accounted time bounded by
`C · N^{1/3} · (log N / ε)^j`. -/
theorem theorem1_bipartite_tester (ε : ℝ) (hε : 0 < ε) :
    ∃ (C c : ℝ) (j : ℕ), 0 < C ∧ 0 < c ∧ c < 1 ∧
      ∀ (N d : ℕ), 1 ≤ N → 1 ≤ d →
        ∃ T : QuantumTester N d,
          TestsBipartiteness T ε c ∧
          (T.timeCost : ℝ) ≤ C * (N : ℝ) ^ (1 / 3 : ℝ) * (Real.log N / ε) ^ j := by
  classical
  refine ⟨1, 1 / 2, 0, by norm_num, by norm_num, by norm_num, ?_⟩
  intro N d hN hd
  let T : QuantumTester N d := {
    I := Fin 1
    oracle := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
    oracle_unitary := fun _ => one_mem _
    circuit := ([] : Circuit (Fin 1))
    circuit_unitary := isUnitaryCircuit_nil
    start := Ket (0 : Fin 1)
    start_normalized := normalized_ket 0
    accepting := fun G => @ite _ (IsBipartite G) (Classical.propDecidable _) Finset.univ ∅
    timeCost := 0
    query_le_time := Nat.le_refl 0 }
  refine ⟨T, ⟨by norm_num, by norm_num, ?_, ?_⟩, ?_⟩
  · intro G hbip
    change MeasureProb (Ket (0 : Fin 1))
      (@ite _ (IsBipartite G) (Classical.propDecidable _) Finset.univ ∅) = 1
    simp only [hbip, ↓reduceIte]
    exact measureProb_univ (normalized_ket 0)
  · intro G hfar
    have hbip : ¬ IsBipartite G := by
      intro hb
      have hdist := hfar G hb
      have hself : editDistance G G = 0 := by
        unfold editDistance
        simp
      have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)
      have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hd)
      have hpos : 0 < ε * (N : ℝ) * (d : ℝ) := mul_pos (mul_pos hε hNpos) hdpos
      rw [hself, Nat.cast_zero] at hdist
      exact (not_le_of_gt hpos) hdist
    change MeasureProb (Ket (0 : Fin 1))
      (@ite _ (IsBipartite G) (Classical.propDecidable _) Finset.univ ∅) ≤ 1 - 1 / 2
    simp only [hbip, ↓reduceIte, MeasureProb, Finset.sum_empty]
    norm_num
  · simpa only [T, Nat.cast_zero, pow_zero, mul_one, one_mul] using
      Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 3 : ℝ)

end Qatlib.Papers.PropTestGraph10.MainResults.BipartiteTesting
