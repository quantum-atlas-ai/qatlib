/-
Copyright (c) 2026 qatlas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-!
# SpectralGap11 reviewed Optimality

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralGap11.MainResults

/-- The black-box optimality setting of Theorem 2 (arXiv:1110.2494v3, p. 5):
`Δ > 0` is the gap of the frustration-free `H` and `Δ' > 0` is the gap of the
optimal amplified Hamiltonian in the class of Theorem 1, evaluated in the
black-box model where the `SEARCH` lower bound applies. The model itself is not
available in the shared libraries; this predicate records its two basic facts. -/
structure BlackBoxOptimalGap (Δ Δ' : ℝ) : Prop where
  /-- The original gap is positive. -/
  gap_pos : 0 < Δ
  /-- The optimal amplified gap is positive. -/
  amp_pos : 0 < Δ'


/-- The legacy pointwise existential constants follow from positivity alone.
The constants depend on both gaps, so this provides no uniform search lower bound. -/
theorem source_theorem2 (Δ Δ' : ℝ) (hmodel : BlackBoxOptimalGap Δ Δ') :
    (∃ c₁ : ℝ, 0 < c₁ ∧ c₁ * Real.sqrt Δ ≤ Δ') ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ Δ' ≤ c₂ * Real.sqrt Δ) := by
  have hs : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hmodel.gap_pos
  have he : Δ' / Real.sqrt Δ * Real.sqrt Δ = Δ' :=
    div_mul_cancel₀ Δ' (ne_of_gt hs)
  exact ⟨⟨Δ' / Real.sqrt Δ, div_pos hmodel.amp_pos hs, he.le⟩,
    ⟨Δ' / Real.sqrt Δ, div_pos hmodel.amp_pos hs, he.ge⟩⟩

end Qatlib.Papers.SpectralGap11.MainResults
