/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Euclidean readout stability for clean state conversion

Proposition 4.6 bounds the Euclidean distance from the circuit output to its clean target.
This module gives the associated real-overlap estimate used in Definition 2.1. A distance at
most `ε` from a unit target gives real overlap at least `1 - ε`. In particular, a distance
at most `δ / 2` suffices for the threshold `√(1 - δ)` when `0 ≤ δ ≤ 1`.
The target includes the workspace in its clean state, and the estimate applies to the whole
output vector given the distance bound.

Source: [LeeEtAl2011], Definition 2.1 and Proposition 4.6
([arXiv:1011.3020v2](https://arxiv.org/abs/1011.3020), printed pp. 3 and 8).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StateConvLee10.StateConvert

/-- A uniform Euclidean error-to-overlap bridge for clean coherent output.  If the actual output
vector is `ε`-close to a normalized target in the complex Euclidean norm, then its real overlap
with that target is at least `1 - ε`; the same estimate also bounds its norm.  The constant `1`
is uniform in the nonempty register dimension [LeeEtAl2011]. -/
theorem source_euclidean_error_to_clean_overlap :
    ∃ C : ℝ, 0 < C ∧
      C ≤ 1 ∧
      1 ≤ C ∧
      ∀ (d : ℕ), 0 < d → ∀ (ψ σ : EuclideanSpace ℂ (Fin d)) (ε : ℝ),
        0 ≤ ε → ‖σ‖ = 1 → ‖ψ - σ‖ ≤ C * ε →
          1 - C * ε ≤ (inner ℂ ψ σ).re ∧ ‖ψ‖ ≤ 1 + C * ε := by
  refine ⟨1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro d _ ψ σ ε hε hσ herr
  have hself : inner ℂ σ σ = 1 := inner_self_eq_one_of_norm_eq_one hσ
  have hsplit : inner ℂ ψ σ = 1 + inner ℂ (ψ - σ) σ := by
    have hadd : σ + (ψ - σ) = ψ := by abel
    have harg : σ + (ψ - σ) - σ = ψ - σ := by abel
    rw [← hadd, inner_add_left, hself, harg]
  have hnormerr : ‖inner ℂ (ψ - σ) σ‖ ≤ ε := by
    calc ‖inner ℂ (ψ - σ) σ‖ ≤ ‖ψ - σ‖ * ‖σ‖ := norm_inner_le_norm _ _
      _ ≤ ε := by
          rw [hσ, mul_one]
          simpa using herr
  have hre : (inner ℂ ψ σ).re = 1 + (inner ℂ (ψ - σ) σ).re := by
    rw [hsplit]
    simp
  constructor
  · rw [hre]
    have habs : |(inner ℂ (ψ - σ) σ).re| ≤ ε := by
      exact (Complex.abs_re_le_norm _).trans hnormerr
    linarith [abs_le.mp habs]
  · have hadd : σ + (ψ - σ) = ψ := by abel
    calc ‖ψ‖ = ‖σ + (ψ - σ)‖ := by rw [hadd]
      _ ≤ ‖σ‖ + ‖ψ - σ‖ := norm_add_le _ _
      _ ≤ 1 + 1 * ε := by
          have hle : ‖ψ - σ‖ ≤ ε := by simpa using herr
          have hsum := add_le_add (le_of_eq hσ) hle
          simpa using hsum

end Qatlib.Papers.StateConvLee10.StateConvert
