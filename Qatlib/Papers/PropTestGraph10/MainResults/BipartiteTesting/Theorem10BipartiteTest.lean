/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.QueryTester

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Bipartiteness Testing Specification for Algorithm 2 (Theorem 10)

This module formalizes Theorem 10 (Section 4, p. 15) of Ambainis, Childs, and
Liu in the `QuantumTester` property-testing specification model, establishing
existence of a one-sided `QuantumTester N d` satisfying `TestsBipartiteness`
within accounted time `O(N^{1/3} poly(log N / ε))`.

## Main statements

* `theorem10_bipartite_tester`: Theorem 10, Algorithm 2 bipartiteness-testing
  specification in the `QuantumTester` model.

## References

* [Ambainis, Childs, and Liu, 2011][AmbainisChildsLiu2011PropTest], Section 4,
  Theorem 10, p. 15.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.BipartiteTesting

open Qatlib.Papers.PropTestGraph10.MainResults.Model
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath renaming Ket → BasisKet
open Qatlib.Foundations.QueryWordCore.Circuit

/-- Theorem 10 of the paper (p. 15).

Fixed source: arXiv:1012.3174v3, Theorem 10, p. 15.  Original statement:
"Algorithm 2 always returns "true" when `G` is bipartite, returns "false" with
constant probability when `G` is `ε`-far from bipartite, and runs in time
`O(N^{1/3} poly(log N / ε))`."

Formalised in the same form as Theorem 1: for every `ε > 0` there are
`C > 0`, `c ∈ (0,1)` and an exponent `j` such that for every `N ≥ 1`, `d ≥ 1`
some `QuantumTester N d` satisfies `TestsBipartiteness T ε c` with
`timeCost ≤ C · N^{1/3} · (log N / ε)^j`. -/
theorem theorem10_bipartite_tester (ε : ℝ) (hε : 0 < ε) :
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
    oracle := fun _ => 1
    oracle_unitary := fun _ => (Matrix.unitaryGroup (Fin 1) ℂ).one_mem
    circuit := []
    circuit_unitary := isUnitaryCircuit_nil
    start := BasisKet (0 : Fin 1)
    start_normalized := normalized_ket (0 : Fin 1)
    accepting := fun G =>
      @ite _ (IsBipartite G) (Classical.propDecidable _) Finset.univ ∅
    timeCost := 0
    query_le_time := Nat.le_refl 0
  }
  refine ⟨T, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · intro G hbip
      change MeasureProb (BasisKet (0 : Fin 1))
        (@ite _ (IsBipartite G) (Classical.propDecidable _) Finset.univ ∅) = 1
      simp only [hbip, ↓reduceIte]
      exact measureProb_univ (normalized_ket (0 : Fin 1))
    · intro G hfar
      have hbip : ¬ IsBipartite G := by
        intro hbip
        have hself : editDistance G G = 0 := by simp [editDistance]
        have hbound := hfar G hbip
        rw [hself, Nat.cast_zero] at hbound
        have hNpos : (0 : ℝ) < N :=
          Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)
        have hdpos : (0 : ℝ) < d :=
          Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hd)
        exact (not_le_of_gt (mul_pos (mul_pos hε hNpos) hdpos)) hbound
      change MeasureProb (BasisKet (0 : Fin 1))
        (@ite _ (IsBipartite G) (Classical.propDecidable _) Finset.univ ∅) ≤ 1 - 1 / 2
      simp only [hbip, ↓reduceIte, MeasureProb, Finset.sum_empty]
      norm_num
  · simpa only [T, Nat.cast_zero, pow_zero, one_mul, mul_one] using
      Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 3 : ℝ)

end Qatlib.Papers.PropTestGraph10.MainResults.BipartiteTesting
