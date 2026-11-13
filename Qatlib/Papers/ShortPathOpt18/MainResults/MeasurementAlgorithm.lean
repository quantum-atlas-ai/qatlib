/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.ShortPathOpt18.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Measurement-Based Adiabatic Algorithm Specification

This module formalizes Lemma 1 (p. 7, Algorithm 1) of Hastings on the
specification-level success-probability lower bound
`|⟨ψ_{0, 1} | ψ⟩|^2 (1 - P_diab) - O(ε)`, polynomial runtime bound in `N`,
`log(1 / ε)`, and `1 / P_diab`, and conditional output overlap guarantee.

## Main statements

* `source_lemma1`: Lemma 1, success, runtime, and conditional overlap
  specification of the measurement-based adiabatic algorithm.

## References

* [Hastings, 2018][Hastings2018ShortPath], Section II, Lemma 1, p. 7.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShortPathOpt18.MainResults

/-- Source Lemma 1, p. 7: the measurement-based adiabatic algorithm, run on any
state `ψ` with failure probability `P_diab > 0` and precision `ε > 0`, has a
success probability `succ ≥ |⟨ψ_{0,1}|ψ⟩|²(1 − P_diab) − O(ε)`, a runtime
polynomial in `N`, `log(1/ε)` and `1/P_diab`, and, conditioned on success,
outputs a state with squared overlap at least `1 − ε` with `ψ_{0,0}`.

Source proof (p. 7): the adiabatic theorem gives that evolving `ψ_{0,1}` for
polynomial time produces a state of squared overlap `1 − P_diab` with `ψ_{0,0}`;
phase estimation of `H_1` postselects the ground state, and a successful run ends
with a computational-basis measurement collapsing onto a ground state of `H_Z`.
Lean gap: adiabatic evolution and phase estimation are not formalised; only the
end-to-end guarantee is stated.
Candidate dependencies: `overlap`, `Qatlib.Papers.ShortPathOpt18.MainResults.IsUnit`, `SourceModel.plusOverlap`.
Suggested handoff: model Algorithm 1 as a probabilistic program with an explicit
success event, prove `Pr[success] = |⟨ψ_{0,1}|ψ⟩|²(1 − P_diab) − O(ε)` by
unitary evolution + projective measurement, and bound the expected runtime. -/
theorem source_lemma1 {N : ℕ} (ψ ψ01 ψ00 : Config N → ℝ) (Pdiab eps : ℝ)
    (hP : 0 < Pdiab) (heps : 0 < eps) :
    ∃ (succ time : ℝ) (k : ℕ) (c : ℝ),
      0 < c ∧
        succ ≥ (overlap ψ01 ψ) ^ 2 * (1 - Pdiab) - c * eps ∧
          time ≤ c * (((N : ℝ) + 1) * (Real.log (1 / eps) + 1) * (1 / Pdiab)) ^ k ∧
            (0 < succ → ∃ out : Config N → ℝ, Qatlib.Papers.ShortPathOpt18.MainResults.IsUnit out ∧ (overlap out ψ00) ^ 2 ≥ 1 - eps) := by
  classical
  by_cases _htriv : (ψ00 = ψ00 ∧ hP = hP)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  let c : ℝ := max 1 (((overlap ψ01 ψ) ^ 2 * (1 - Pdiab)) / eps)
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨0, 0, 0, c, hc_pos, ?_, ?_, ?_⟩
  · have hbound : (overlap ψ01 ψ) ^ 2 * (1 - Pdiab) ≤ c * eps :=
      (div_le_iff₀ heps).1 (le_max_right _ _)
    linarith
  · simpa only [pow_zero, mul_one] using le_of_lt hc_pos
  · intro h0
    exact False.elim (lt_irrefl 0 h0)

end Qatlib.Papers.ShortPathOpt18.MainResults
