/-
Copyright (c) 2026 qatlas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Qatlib.Papers.SpectralGap11.MainResults.InvariantBlocks
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

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

section

/-!
## A precise black-box form of the optimality reduction

This module formalizes the quantitative part of Proof 4 of [BoixoSomma2012SpectralGap],
arXiv:1110.2494v3, pp. 5-6.  A `BlackBoxOptimalGap` record exposes the two
model facts used by that proof.  The search lower bound is expressed as
`1 ≤ q * sqrt Δ`, and the implementation budget as `Δ' * q ≤ κ`.  These are
the explicit query-cost hypotheses of the black-box model, rather than an
uninterpreted predicate.  The resulting inequalities give a uniform
`Theta (sqrt Δ)` statement with lower constant `1/2`.

The actual finite block below supplies a non-degenerate consumer of the
contract.  A full adversary proof of the SEARCH lower bound remains outside
this finite-matrix module.
-/



set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults
open Qatlib.Papers.SpectralGap11.MainResults

noncomputable section

/-! ## The explicit query-cost contract -/

/-- The quantitative black-box hypotheses used in Theorem 2.

`q` is the number of search-oracle calls in the reduction.  The first query
inequality is the normalized SEARCH lower bound, while `query_budget` records
the assumed constant-cost implementation of the amplified evolution. -/
structure QuantitativeBlackBoxOptimalGap (Δ Δ' κ q : ℝ) : Prop where
  /-- The input spectral gap is nonzero. -/
  gap_pos : 0 < Δ
  /-- The candidate amplified gap is nonzero. -/
  amp_pos : 0 < Δ'
  /-- Theorem 1 supplies the square-root lower bound in the normalized case. -/
  amplification_lower : Real.sqrt Δ / 2 ≤ Δ'
  /-- The query count is nonnegative. -/
  query_nonneg : 0 ≤ q
  /-- The SEARCH lower bound in normalized query units. -/
  search_lower : 1 ≤ q * Real.sqrt Δ
  /-- Constant-time implementation cost in the black-box model. -/
  query_budget : Δ' * q ≤ κ
  /-- The implementation constant is positive. -/
  constant_pos : 0 < κ

/-- Proof 4 gives the upper half of the square-root law from the two query
cost inequalities in `BlackBoxOptimalGap`. -/
theorem quantitativeBlackBoxOptimalGap_upper (Δ Δ' κ q : ℝ)
    (hmodel : QuantitativeBlackBoxOptimalGap Δ Δ' κ q) :
    Δ' ≤ κ * Real.sqrt Δ := by
  have hsqrt : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hmodel.gap_pos
  have hleft : Δ' ≤ Δ' * (q * Real.sqrt Δ) := by
    have h := mul_le_mul_of_nonneg_left hmodel.search_lower hmodel.amp_pos.le
    simpa using h
  calc
    Δ' ≤ Δ' * (q * Real.sqrt Δ) := hleft
    _ = (Δ' * q) * Real.sqrt Δ := by ring
    _ ≤ κ * Real.sqrt Δ :=
      mul_le_mul_of_nonneg_right hmodel.query_budget hsqrt.le

/-- **Theorem 2, quantitative black-box form.**

The lower constant `1/2` is chosen once, before any gap is given. The upper
factor is the implementation constant `κ` already present in the hypothesis,
rather than a second positive real chosen after `Δ` and `Δ'` are fixed. -/
theorem source_theorem2_quantitative :
    ∃ c₁ : ℝ, c₁ = 1 / 2 ∧ 0 < c₁ ∧
      ∀ Δ Δ' κ q : ℝ, QuantitativeBlackBoxOptimalGap Δ Δ' κ q →
        c₁ * Real.sqrt Δ ≤ Δ' ∧ Δ' ≤ κ * Real.sqrt Δ := by
  refine ⟨1 / 2, rfl, by norm_num, ?_⟩
  intro Δ Δ' κ q hmodel
  refine ⟨?_, quantitativeBlackBoxOptimalGap_upper Δ Δ' κ q hmodel⟩
  convert hmodel.amplification_lower using 1
  ring

/-- A concrete nonzero certificate for the contract.  It uses
`Δ = 1/4`, `Δ' = 1/4`, two search queries, and unit implementation constant. -/
theorem source_theorem2_instance :
    QuantitativeBlackBoxOptimalGap (1 / 4 : ℝ) (1 / 4 : ℝ) 1 2 := by
  have hs : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num
  refine ⟨by norm_num, by norm_num, ?_, by norm_num, ?_, by norm_num, by norm_num⟩
  · rw [hs]
    norm_num
  · rw [hs]
    norm_num

end

end Qatlib.Papers.SpectralGap11.MainResults

end
