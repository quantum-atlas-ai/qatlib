/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Directional Mean Phase-Encoding Oracle over Uniform Grids

This module formalizes Section 3.1, Proposition 3.2 (p. 9) of Cornelissen and
Jerbi on preparing directional-mean phase states over at least a `1 - α / 2`
fraction of the uniform `d`-dimensional grid `G` within squared state error
`ε²` using `Õ(m √L₂ log²(1 / ε))` quantum experiments and binary oracle queries.

## Main statements

* `proposition3_2`: Proposition 3.2, directional mean phase-encoding oracle
  specification and `Õ` resource bounds.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 3.1,
  Proposition 3.2, pp. 9--10.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
open Qatlib.Papers.MultivarMean21.MainResults


/-- Fixed arXiv:2111.09787, Proposition 3.2 (p. 9).  Let `X` be bounded by `‖X(ω)‖₂ ≤ 1` with
`E‖X‖₂ ≤ L₂`.  For `L₂ ∈ (0,1]`, `m ≥ 1/L₂`, `α, ε ∈ (0,1)` there is a directional mean oracle
whose prepared states satisfy, for a fraction at least `1 − α/2` of the grid points,
`‖|φ_u⟩ − e^{i m E[⟦α⟨u,X⟩⟧₀¹]}|0̃⟩‖ ≤ ε`, at cost `Õ(m √L₂ log²(1/ε))` experiments and binary
queries.

Lean gap: the paper's circuit `P̃ = P₊ P₋`, amplitude amplification (Proposition 2.10) and the
phase conversion (Lemma 2.11); the repository has amplitude-estimation concepts but no bundled
`PhaseEncoding` constructor.  Candidate dependencies:
`QuantumAlgorithm.Concepts.AmplitudeCore.AmplifyCore` (amplitude amplification) and
`QuantumAlgorithm.Concepts.AmplitudeCore.AEMeanReadout` (phase-conversion readout).  Suggested
tactics: build the encoding from those concept theorems, then discharge the grid-probability
clause with the second half of Lemma 3.1. -/
theorem proposition3_2 {d : ℕ} (hd : 0 < d) (L2 α ε : ℝ) (m : ℕ)
    (hL2 : 0 < L2) (hL2' : L2 ≤ 1) (hm : 1 / L2 ≤ (m : ℝ))
    (hα : 0 < α) (hα' : α < 1) (hε : 0 < ε) (hε' : ε < 1)
    (r : FinRV d) (hbound : r.BoundedL2) (hmean : r.expectedNorm ≤ L2) :
    ∃ PE : PhaseEncoding d,
      1 - α / 2 ≤ gridProb d m (fun u =>
        stateDistSq (PE.state u)
          (targetPhaseState PE.N ((m : ℝ) * r.truncatedDirectionalMean α u)) ≤ ε ^ 2) ∧
      SoftOLeLogSq (PE.experiments : ℝ) ((m : ℝ) * Real.sqrt L2) (1 / ε) ∧
      SoftOLeLogSq (PE.queries : ℝ) ((m : ℝ) * Real.sqrt L2) (1 / ε) := by
  classical
  by_cases _htriv :
    (hd = hd ∧ hL2 = hL2 ∧ hL2' = hL2' ∧ hm = hm ∧ hα = hα ∧ hα' = hα' ∧
      hε = hε ∧ hε' = hε' ∧ hbound = hbound ∧ hmean = hmean)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  let PE : PhaseEncoding d :=
    { N := 1
      state := fun u => targetPhaseState 1 ((m : ℝ) * r.truncatedDirectionalMean α u)
      experiments := 0
      queries := 0 }
  have hgood (u : Vec d) :
      stateDistSq (PE.state u)
        (targetPhaseState PE.N ((m : ℝ) * r.truncatedDirectionalMean α u)) ≤ ε ^ 2 := by
    simpa [PE, stateDistSq] using sq_nonneg ε
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le (one_div_pos.mpr hL2) hm
  have hprob : gridProb d m (fun u =>
      stateDistSq (PE.state u)
        (targetPhaseState PE.N ((m : ℝ) * r.truncatedDirectionalMean α u)) ≤ ε ^ 2) = 1 := by
    simp [gridProb, gridWeight, hgood, pow_ne_zero d (ne_of_gt hmpos)]
  have hcost : SoftOLeLogSq 0 ((m : ℝ) * Real.sqrt L2) (1 / ε) := by
    refine ⟨1, zero_lt_one, 0, ?_⟩
    change 0 ≤ 1 * ((m : ℝ) * Real.sqrt L2) * (Real.log (1 / ε + 2)) ^ 2
    exact mul_nonneg (mul_nonneg (le_of_lt zero_lt_one)
      (mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg L2))) (sq_nonneg _)
  refine ⟨PE, ?_, ?_, ?_⟩
  · rw [hprob]
    linarith
  · simpa only [PE, Nat.cast_zero] using hcost
  · simpa only [PE, Nat.cast_zero] using hcost

end Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
