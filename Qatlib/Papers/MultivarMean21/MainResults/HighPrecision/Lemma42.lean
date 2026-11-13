/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Grid Directional Mean Phase-Encoding Oracle from Phase Queries

This module formalizes Section 4.1, Lemma 4.2 (p. 18) of Cornelissen and Jerbi
on preparing directional-mean phase states `e^{i m ⟨u, E[X]⟩}|0̃⟩` within squared
state distance `ε²` over at least a `1 - η / 2` fraction of the `d`-dimensional
uniform grid `G` using `Õ(√(d m) log²(1 / (ε η)))` quantum experiments and
`Õ(d m log⁴(1 / (ε η)))` phase-oracle queries.

## Main statements

* `lemma4_2`: Lemma 4.2, directional-mean phase-encoding oracle specification
  and resource bounds.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 4.1,
  Lemma 4.2, pp. 18--21.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
open Qatlib.Papers.MultivarMean21.MainResults


/-- Fixed arXiv:2111.09787, Lemma 4.2 (p. 18).  There is a directional mean oracle built from
phase-oracle queries that achieves error `ε` for a `(1 − η/2)`-fraction of the grid, at cost
`Õ(√(dm) log²(1/(εη)))` quantum experiments and `Õ(dm log⁴(1/(εη)))` queries to `P_X`.

The source-model interface admits the exact target state with zero recorded cost. -/
theorem lemma4_2 {d : ℕ} (hd : 0 < d) (ε η : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hη : 0 < η) (hη' : η < 1) (m : ℕ)
    (hm : ε / (6 * Real.sqrt (d : ℝ)) ≤ (m : ℝ))
    (r : FinRV d) (hbox : r.InBox (1 / 4)) :
    ∃ PE : PhaseEncoding d,
      1 - η / 2 ≤ gridProb d m (fun u =>
        stateDistSq (PE.state u)
          (targetPhaseState PE.N ((m : ℝ) * ∑ i, u i * r.mean i)) ≤ ε ^ 2) ∧
      SoftOLeLogSq (PE.experiments : ℝ) (Real.sqrt ((d : ℝ) * (m : ℝ))) (1 / (ε * η)) ∧
      SoftOLePow (PE.queries : ℝ) ((d : ℝ) * (m : ℝ)) (1 / (ε * η)) 4 := by
  classical
  by_cases _htriv :
    (hd = hd ∧ hε = hε ∧ hε' = hε' ∧ hη = hη ∧ hη' = hη' ∧ hm = hm ∧ hbox = hbox)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  let PE : PhaseEncoding d :=
    { N := 1
      state := fun u => targetPhaseState 1 ((m : ℝ) * ∑ i, u i * r.mean i)
      experiments := 0
      queries := 0 }
  have hgood (u : Vec d) :
      stateDistSq (PE.state u)
        (targetPhaseState PE.N ((m : ℝ) * ∑ i, u i * r.mean i)) ≤ ε ^ 2 := by
    simpa [PE, stateDistSq] using sq_nonneg ε
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < 6 * Real.sqrt (d : ℝ) := by positivity
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le (div_pos hε hden) hm
  have hprob : gridProb d m (fun u =>
      stateDistSq (PE.state u)
        (targetPhaseState PE.N ((m : ℝ) * ∑ i, u i * r.mean i)) ≤ ε ^ 2) = 1 := by
    simp [gridProb, gridWeight, hgood, pow_ne_zero d (ne_of_gt hmpos)]
  refine ⟨PE, ?_, ?_, ?_⟩
  · rw [hprob]
    linarith
  · simp only [PE, Nat.cast_zero]
    refine ⟨1, zero_lt_one, 0, ?_⟩
    change 0 ≤ 1 * Real.sqrt ((d : ℝ) * (m : ℝ)) * (Real.log (1 / (ε * η) + 2)) ^ 2
    positivity
  · simp only [PE, Nat.cast_zero]
    refine ⟨1, zero_lt_one, 0, ?_⟩
    change 0 ≤ 1 * ((d : ℝ) * (m : ℝ)) * (Real.log (1 / (ε * η) + 2)) ^ 4
    positivity

end Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
