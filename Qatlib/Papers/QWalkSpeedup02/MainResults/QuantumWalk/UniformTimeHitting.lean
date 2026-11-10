/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.SpectralHitting
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.UniformTimeHitting

open Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.SpectralHitting

theorem theorem3_uniform_time_hitting {n N : ℕ} (S : SpectralWalk n N)
    (hN : N ≤ 2 * n) {ε : ℝ} (hε : 0 < ε) (hn : 1 ≤ n)
    (hgap : ∀ i j : Fin N, i ≠ j → 8 / (n : ℝ) ^ 3 ≤ |S.energy i - S.energy j|) :
    (1 / (2 * (n : ℝ))) * (1 - ε) ≤
      S.timeAveragedExitProbability ((n : ℝ) ^ 4 / (2 * ε)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine SpectralWalk.lemma1_hitting_probability (n := n) (N := N) S hN
    (ε := ε) (ΔE := 8 / (n : ℝ) ^ 3) (τ := (n : ℝ) ^ 4 / (2 * ε)) hε ?_ hgap ?_
  · exact div_pos (by norm_num) (pow_pos hnpos 3)
  · have hEq : 4 * (n : ℝ) / (ε * (8 / (n : ℝ) ^ 3)) = (n : ℝ) ^ 4 / (2 * ε) := by
      have hεne : ε ≠ 0 := ne_of_gt hε
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp
      ring
    rw [hEq]

end Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.UniformTimeHitting
