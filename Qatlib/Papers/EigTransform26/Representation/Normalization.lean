/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.EigTransform26.Representation.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Nonzero normalization regression

The constant polynomial one has lift norm one, rather than the former zero stub.
-/

namespace Qatlib.Papers.EigTransform26.Representation

/-- A nonzero constant lift has its genuine unit-circle norm. -/
theorem liftNormalization_one : liftNormalization (1 : Polynomial ℂ) = 1 := by
  unfold liftNormalization
  have hs : {r : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
      r = ‖2 * Polynomial.eval z (1 : Polynomial ℂ) - Polynomial.eval 0 (1 : Polynomial ℂ)‖} =
      {1} := by
    ext r
    constructor
    · rintro ⟨z, _, hr⟩
      norm_num at hr
      exact hr
    · intro hr
      refine ⟨1, norm_one, ?_⟩
      norm_num
      exact hr
  rw [hs, csSup_singleton]

end Qatlib.Papers.EigTransform26.Representation
